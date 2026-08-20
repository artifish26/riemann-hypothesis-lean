import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualTailBounds

/-!
# Sharp leading residual tails for M100-DF6D4

The odd leading tail is a single inverse-square rank-one form.  The even
leading tail keeps the prime-2 oscillation: its exact quadratic form is the
sum of the ordinary inverse-square tail, a sine-square tail, and the signed
sine cross tail.  Keeping this identity exact is essential for the frozen
FT3 reserve.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators

def suzukiDF6D4PrimeTailPhase : Real :=
  Real.pi * Real.log 2 / suzukiProjectAStar

def suzukiDF6D4PrimeTailAmplitude : Real :=
  Real.sqrt 2 * Real.log 2

def suzukiDF6D4PrimeSineInverseSquareTail : Real :=
  ∑' k : Nat,
    Real.sin (((601 + k : Nat) : Real) * suzukiDF6D4PrimeTailPhase) /
      (((601 + k : Nat) : Real) ^ 2)

def suzukiDF6D4PrimeSineSquareInverseSquareTail : Real :=
  ∑' k : Nat,
    Real.sin (((601 + k : Nat) : Real) * suzukiDF6D4PrimeTailPhase) ^ 2 /
      (((601 + k : Nat) : Real) ^ 2)

private theorem suzukiDF6D4ShiftedInverseSquare_summable :
    Summable fun k : Nat =>
      1 / (((601 + k : Nat) : Real) ^ 2) := by
  have hbase : Summable (fun n : Nat => 1 / ((n : Real) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff
    (f := fun n : Nat => 1 / ((n : Real) ^ 2)) 601).2 hbase
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift

theorem suzukiDF6D4PrimeSineInverseSquare_summable :
    Summable fun k : Nat =>
      Real.sin (((601 + k : Nat) : Real) * suzukiDF6D4PrimeTailPhase) /
        (((601 + k : Nat) : Real) ^ 2) := by
  refine suzukiDF6D4ShiftedInverseSquare_summable.of_norm_bounded fun k => ?_
  have hden : 0 < (((601 + k : Nat) : Real) ^ 2) := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
  exact (div_le_div_iff_of_pos_right hden).2 (Real.abs_sin_le_one _)

theorem suzukiDF6D4PrimeSineSquareInverseSquare_summable :
    Summable fun k : Nat =>
      Real.sin (((601 + k : Nat) : Real) * suzukiDF6D4PrimeTailPhase) ^ 2 /
        (((601 + k : Nat) : Real) ^ 2) := by
  refine suzukiDF6D4ShiftedInverseSquare_summable.of_norm_bounded fun k => ?_
  have hden : 0 < (((601 + k : Nat) : Real) ^ 2) := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos hden]
  exact (div_le_div_iff_of_pos_right hden).2 (Real.sin_sq_le_one _)

private theorem suzukiDF6D4TailParity_real_sq (mode : Nat) :
    ((((suzukiDF6D4TailParity mode : Rat) : Real)) ^ 2) = 1 := by
  rw [← sq_abs, suzukiDF6D4TailParity_real_abs]
  norm_num

private theorem suzukiDF6D4EvenResidualTailMain_dot
    (mode : Nat) (x : Fin 45 → Real) :
    (∑ i, x i * suzukiDF6D4EvenResidualTailMain mode i) =
      (((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
        (-(Real.pi / 2) *
            (∑ i, x i * suzukiDF6D4EvenResidualTailTransformMoment 0 i) /
              (mode : Real) +
          (∑ i, x i * suzukiDF6D4EvenTailTransformMoment 0
              (suzukiDF6D4EvenLowMode i)) *
            suzukiDF6D4PrimeSineTransform mode / (mode : Real)) := by
  unfold suzukiDF6D4EvenResidualTailMain
  calc
    (∑ i, x i *
        ((((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
          (-(Real.pi / 2) * suzukiDF6D4EvenResidualTailTransformMoment 0 i /
                (mode : Real) +
            suzukiDF6D4EvenTailTransformMoment 0
                (suzukiDF6D4EvenLowMode i) *
              suzukiDF6D4PrimeSineTransform mode / (mode : Real)))) =
        ∑ i, ((((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹) *
          (x i *
            (-(Real.pi / 2) * suzukiDF6D4EvenResidualTailTransformMoment 0 i /
                  (mode : Real) +
              suzukiDF6D4EvenTailTransformMoment 0
                  (suzukiDF6D4EvenLowMode i) *
                suzukiDF6D4PrimeSineTransform mode / (mode : Real))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
        ∑ i, x i *
          (-(Real.pi / 2) * suzukiDF6D4EvenResidualTailTransformMoment 0 i /
                (mode : Real) +
            suzukiDF6D4EvenTailTransformMoment 0
                (suzukiDF6D4EvenLowMode i) *
              suzukiDF6D4PrimeSineTransform mode / (mode : Real)) := by
      rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      rw [show (∑ i, x i *
          (-(Real.pi / 2) * suzukiDF6D4EvenResidualTailTransformMoment 0 i /
                (mode : Real) +
            suzukiDF6D4EvenTailTransformMoment 0
                (suzukiDF6D4EvenLowMode i) *
              suzukiDF6D4PrimeSineTransform mode / (mode : Real))) =
          ∑ i, (x i * (-(Real.pi / 2) *
              suzukiDF6D4EvenResidualTailTransformMoment 0 i /
                (mode : Real)) +
            x i * (suzukiDF6D4EvenTailTransformMoment 0
                (suzukiDF6D4EvenLowMode i) *
              suzukiDF6D4PrimeSineTransform mode / (mode : Real))) by
        apply Finset.sum_congr rfl
        intro i _
        ring]
      rw [Finset.sum_add_distrib]
      congr 1
      · calc
          (∑ i, x i *
              (-(Real.pi / 2) *
                suzukiDF6D4EvenResidualTailTransformMoment 0 i /
                  (mode : Real))) =
              ∑ i, (x i * suzukiDF6D4EvenResidualTailTransformMoment 0 i) *
                (-(Real.pi / 2) / (mode : Real)) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  ring
          _ = (∑ i, x i * suzukiDF6D4EvenResidualTailTransformMoment 0 i) *
              (-(Real.pi / 2) / (mode : Real)) := by rw [Finset.sum_mul]
          _ = -(Real.pi / 2) *
              (∑ i, x i * suzukiDF6D4EvenResidualTailTransformMoment 0 i) /
                (mode : Real) := by ring
      · calc
          (∑ i, x i *
              (suzukiDF6D4EvenTailTransformMoment 0
                  (suzukiDF6D4EvenLowMode i) *
                suzukiDF6D4PrimeSineTransform mode / (mode : Real))) =
              ∑ i, (x i * suzukiDF6D4EvenTailTransformMoment 0
                  (suzukiDF6D4EvenLowMode i)) *
                (suzukiDF6D4PrimeSineTransform mode / (mode : Real)) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  ring
          _ = (∑ i, x i * suzukiDF6D4EvenTailTransformMoment 0
                  (suzukiDF6D4EvenLowMode i)) *
                (suzukiDF6D4PrimeSineTransform mode / (mode : Real)) := by
            rw [Finset.sum_mul]
          _ = (∑ i, x i * suzukiDF6D4EvenTailTransformMoment 0
                  (suzukiDF6D4EvenLowMode i)) *
                suzukiDF6D4PrimeSineTransform mode / (mode : Real) := by ring

private theorem suzukiDF6D4OddResidualTailMain_dot
    (mode : Nat) (x : Fin 44 → Real) :
    (∑ i, x i * suzukiDF6D4OddResidualTailMain mode i) =
      -(((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
        (∑ i, x i * suzukiDF6D4OddResidualTailFixedMoment 0 i) /
          (mode : Real) := by
  unfold suzukiDF6D4OddResidualTailMain
  rw [show (∑ i, x i *
      ((((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
        (-suzukiDF6D4OddResidualTailFixedMoment 0 i / (mode : Real)))) =
      ∑ i, (x i * suzukiDF6D4OddResidualTailFixedMoment 0 i) *
        (-(((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ /
          (mode : Real)) by
    apply Finset.sum_congr rfl
    intro i _
    ring]
  calc
    (∑ i, (x i * suzukiDF6D4OddResidualTailFixedMoment 0 i) *
        (-(((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ /
          (mode : Real))) =
        (∑ i, x i * suzukiDF6D4OddResidualTailFixedMoment 0 i) *
          (-(((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ /
            (mode : Real)) := by rw [Finset.sum_mul]
    _ = _ := by ring

def suzukiDF6D4EvenResidualTailMainQuadratic
    (x : Fin 45 → Real) : Real :=
  let transformDot :=
    ∑ i, x i * suzukiDF6D4EvenResidualTailTransformMoment 0 i
  let lowDot :=
    ∑ i, x i * suzukiDF6D4EvenTailTransformMoment 0
      (suzukiDF6D4EvenLowMode i)
  Real.pi⁻¹ ^ 2 *
    ((Real.pi ^ 2 / 4) * suzukiDF6D4InverseSquareTail 600 *
        transformDot ^ 2 +
      suzukiDF6D4PrimeTailAmplitude ^ 2 *
        suzukiDF6D4PrimeSineSquareInverseSquareTail * lowDot ^ 2 +
      Real.pi * suzukiDF6D4PrimeTailAmplitude *
        suzukiDF6D4PrimeSineInverseSquareTail * transformDot * lowDot)

def suzukiDF6D4OddResidualTailMainQuadratic
    (x : Fin 44 → Real) : Real :=
  Real.pi⁻¹ ^ 2 * suzukiDF6D4InverseSquareTail 600 *
    (∑ i, x i * suzukiDF6D4OddResidualTailFixedMoment 0 i) ^ 2

theorem suzukiDF6D4EvenResidualTailMainQuadratic_eq
    (x : Fin 45 → Real) :
    (∑' k : Nat,
      (∑ i, x i * suzukiDF6D4EvenResidualTailMain (601 + k) i) ^ 2) =
      suzukiDF6D4EvenResidualTailMainQuadratic x := by
  let transformDot :=
    ∑ i, x i * suzukiDF6D4EvenResidualTailTransformMoment 0 i
  let lowDot :=
    ∑ i, x i * suzukiDF6D4EvenTailTransformMoment 0
      (suzukiDF6D4EvenLowMode i)
  let inv := fun k : Nat => 1 / (((601 + k : Nat) : Real) ^ 2)
  let sine := fun k : Nat =>
    Real.sin (((601 + k : Nat) : Real) * suzukiDF6D4PrimeTailPhase) /
      (((601 + k : Nat) : Real) ^ 2)
  let sineSq := fun k : Nat =>
    Real.sin (((601 + k : Nat) : Real) * suzukiDF6D4PrimeTailPhase) ^ 2 /
      (((601 + k : Nat) : Real) ^ 2)
  have hinv : Summable inv := by
    simpa only [inv] using suzukiDF6D4ShiftedInverseSquare_summable
  have hsine : Summable sine := by
    simpa only [sine] using suzukiDF6D4PrimeSineInverseSquare_summable
  have hsineSq : Summable sineSq := by
    simpa only [sineSq] using suzukiDF6D4PrimeSineSquareInverseSquare_summable
  have hpoint : ∀ k : Nat,
      (∑ i, x i * suzukiDF6D4EvenResidualTailMain (601 + k) i) ^ 2 =
        (Real.pi⁻¹ ^ 2 * (Real.pi ^ 2 / 4) * transformDot ^ 2) * inv k +
        (Real.pi⁻¹ ^ 2 * suzukiDF6D4PrimeTailAmplitude ^ 2 * lowDot ^ 2) *
          sineSq k +
        (Real.pi⁻¹ ^ 2 * Real.pi * suzukiDF6D4PrimeTailAmplitude *
          transformDot * lowDot) * sine k := by
    intro k
    rw [suzukiDF6D4EvenResidualTailMain_dot]
    have hparity := suzukiDF6D4TailParity_real_sq (601 + k)
    unfold suzukiDF6D4PrimeSineTransform suzukiDF6D4PrimeTailAmplitude
    dsimp only [transformDot, lowDot, inv, sine, sineSq]
    have hangle : ((601 + k : Nat) : Real) * Real.pi * Real.log 2 /
        suzukiProjectAStar =
        ((601 + k : Nat) : Real) *
          suzukiDF6D4PrimeTailPhase := by
      unfold suzukiDF6D4PrimeTailPhase
      ring
    rw [hangle]
    calc
      ((((suzukiDF6D4TailParity (601 + k) : Rat) : Real)) * Real.pi⁻¹ *
          (-(Real.pi / 2) * transformDot / ((601 + k : Nat) : Real) +
            lowDot *
              (-Real.sqrt 2 * Real.log 2 *
                Real.sin (((601 + k : Nat) : Real) *
                  suzukiDF6D4PrimeTailPhase)) /
                ((601 + k : Nat) : Real))) ^ 2 =
          ((((suzukiDF6D4TailParity (601 + k) : Rat) : Real)) ^ 2) *
            (Real.pi⁻¹ ^ 2 * (Real.pi ^ 2 / 4) * transformDot ^ 2 * inv k +
              Real.pi⁻¹ ^ 2 * (Real.sqrt 2 * Real.log 2) ^ 2 * lowDot ^ 2 *
                sineSq k +
                  Real.pi⁻¹ ^ 2 * Real.pi * (Real.sqrt 2 * Real.log 2) *
                transformDot * lowDot * sine k) := by
          dsimp only [inv, sine, sineSq]
          ring
      _ = _ := by
        dsimp only [transformDot, lowDot, inv, sine, sineSq]
        rw [hparity]
        ring
  rw [tsum_congr hpoint]
  have hfirst := hinv.mul_left
    (Real.pi⁻¹ ^ 2 * (Real.pi ^ 2 / 4) * transformDot ^ 2)
  have hsecond := hsineSq.mul_left
    (Real.pi⁻¹ ^ 2 * suzukiDF6D4PrimeTailAmplitude ^ 2 * lowDot ^ 2)
  have hthird := hsine.mul_left
    (Real.pi⁻¹ ^ 2 * Real.pi * suzukiDF6D4PrimeTailAmplitude *
      transformDot * lowDot)
  rw [(hfirst.add hsecond).tsum_add hthird, hfirst.tsum_add hsecond]
  simp only [tsum_mul_left]
  unfold suzukiDF6D4EvenResidualTailMainQuadratic
    suzukiDF6D4PrimeSineInverseSquareTail
    suzukiDF6D4PrimeSineSquareInverseSquareTail
  rw [suzukiDF6D4InverseSquareTail_eq_inversePowerTail,
    suzukiDF6D4InversePowerTail_eq_tsum_one_div]
  dsimp only [transformDot, lowDot, inv, sine, sineSq]
  ring

theorem suzukiDF6D4OddResidualTailMainQuadratic_eq
    (x : Fin 44 → Real) :
    (∑' k : Nat,
      (∑ i, x i * suzukiDF6D4OddResidualTailMain (601 + k) i) ^ 2) =
      suzukiDF6D4OddResidualTailMainQuadratic x := by
  let fixedDot :=
    ∑ i, x i * suzukiDF6D4OddResidualTailFixedMoment 0 i
  have hpoint : ∀ k : Nat,
      (∑ i, x i * suzukiDF6D4OddResidualTailMain (601 + k) i) ^ 2 =
        (Real.pi⁻¹ ^ 2 * fixedDot ^ 2) *
          (1 / (((601 + k : Nat) : Real) ^ 2)) := by
    intro k
    rw [suzukiDF6D4OddResidualTailMain_dot]
    have hparity := suzukiDF6D4TailParity_real_sq (601 + k)
    dsimp only [fixedDot]
    calc
      ((-(((suzukiDF6D4TailParity (601 + k) : Rat) : Real)) * Real.pi⁻¹ *
          fixedDot) / ((601 + k : Nat) : Real)) ^ 2 =
        ((((suzukiDF6D4TailParity (601 + k) : Rat) : Real)) ^ 2) *
          (Real.pi⁻¹ ^ 2 * fixedDot ^ 2 *
            (1 / (((601 + k : Nat) : Real) ^ 2))) := by ring
      _ = _ := by
        dsimp only [fixedDot]
        rw [hparity]
        ring
  rw [tsum_congr hpoint, tsum_mul_left]
  unfold suzukiDF6D4OddResidualTailMainQuadratic
  rw [suzukiDF6D4InverseSquareTail_eq_inversePowerTail,
    suzukiDF6D4InversePowerTail_eq_tsum_one_div]
  dsimp only [fixedDot]
  ring

end

end RiemannHypothesisProject.Experiments.M100
