import RiemannHypothesisProject.LiCriterion.ZetaZeroHeightDecay

/-!
# Canonical zeta-zero height decay without a low-zero hypothesis

The dyadic argument only needs the published Riemann-von Mangoldt estimate in
the tail.  Clamping positive ordinates below `1` to height `1` puts the finite
low-height prefix into shell zero and removes the separate zero-free-band
hypothesis from inverse-square summability.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- Positive ordinate clamped to the first dyadic scale. -/
def positiveOrdinateZetaZeroClampedHeight
    (rho : PositiveOrdinateZetaZeroSubtype) : Real :=
  max 1 (Complex.im (rho : Complex))

/-- The dyadic index of the clamped positive ordinate. -/
def positiveOrdinateZetaZeroClampedDyadicShellIndex
    (rho : PositiveOrdinateZetaZeroSubtype) : Nat :=
  realDyadicShellIndex (positiveOrdinateZetaZeroClampedHeight rho)

/-- Actual positive-ordinate zeta zeroes in a clamped dyadic shell. -/
abbrev PositiveOrdinateZetaZeroClampedDyadicShell (m : Nat) :=
  {rho : PositiveOrdinateZetaZeroSubtype //
    positiveOrdinateZetaZeroClampedDyadicShellIndex rho = m}

theorem positiveOrdinateZetaZeroClampedDyadicShellIndex_lower
    (rho : PositiveOrdinateZetaZeroSubtype) :
    (2 : Real) ^ positiveOrdinateZetaZeroClampedDyadicShellIndex rho <=
      positiveOrdinateZetaZeroClampedHeight rho := by
  exact realDyadicShellIndex_lower (le_max_left 1 _)

theorem positiveOrdinateZetaZeroClampedDyadicShellIndex_lt_upper
    (rho : PositiveOrdinateZetaZeroSubtype) :
    positiveOrdinateZetaZeroClampedHeight rho <
      (2 : Real) ^ (positiveOrdinateZetaZeroClampedDyadicShellIndex rho + 1) := by
  exact realDyadicShellIndex_lt_upper (le_max_left 1 _)

/-- Every clamped shell embeds in the corresponding exact positive-height window. -/
def positiveOrdinateZetaZeroClampedDyadicShellEmbedding
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (m : Nat) :
    PositiveOrdinateZetaZeroClampedDyadicShell m ↪
      {rho : ZetaZeroSubtype //
        rho ∈ exactWindow.window ((2 : Real) ^ (m + 1))} where
  toFun rho := by
    refine ⟨rho.1.1, (exactWindow.mem_window_iff _ rho.1.1).mpr ⟨rho.1.2, ?_⟩⟩
    have hupper :=
      positiveOrdinateZetaZeroClampedDyadicShellIndex_lt_upper rho.1
    rw [rho.2] at hupper
    exact (le_max_right 1 (Complex.im (rho.1 : Complex))).trans
      hupper.le
  inj' := by
    intro rho sigma h
    have hzeta : rho.1.1 = sigma.1.1 := congrArg (fun z => z.1) h
    exact Subtype.ext (Subtype.ext hzeta)

@[reducible] def positiveOrdinateZetaZeroClampedDyadicShellFintype
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (m : Nat) :
    Fintype (PositiveOrdinateZetaZeroClampedDyadicShell m) := by
  letI : Finite (PositiveOrdinateZetaZeroClampedDyadicShell m) :=
    Finite.of_injective
      (positiveOrdinateZetaZeroClampedDyadicShellEmbedding exactWindow m)
      (positiveOrdinateZetaZeroClampedDyadicShellEmbedding exactWindow m).injective
  exact Fintype.ofFinite _

/-- Clamping at height `1` changes inverse-square decay by at most a factor of five. -/
theorem positiveOrdinateZetaZero_heightDecay_le_five_mul_clamped
    (rho : PositiveOrdinateZetaZeroSubtype) :
    (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ <=
      5 * (positiveOrdinateZetaZeroClampedHeight rho ^ 2 +
        (1 / 2 : Real) ^ 2)⁻¹ := by
  let t : Real := Complex.im (rho : Complex)
  have ht : 0 < t := rho.2
  have ha : 0 < t ^ 2 + (1 / 2 : Real) ^ 2 := by positivity
  have hb :
      0 < positiveOrdinateZetaZeroClampedHeight rho ^ 2 +
        (1 / 2 : Real) ^ 2 := by positivity
  have hden :
      positiveOrdinateZetaZeroClampedHeight rho ^ 2 +
          (1 / 2 : Real) ^ 2 <=
        5 * (t ^ 2 + (1 / 2 : Real) ^ 2) := by
    change max 1 t ^ 2 + (1 / 2 : Real) ^ 2 <=
      5 * (t ^ 2 + (1 / 2 : Real) ^ 2)
    by_cases ht_one : t <= 1
    · rw [max_eq_left ht_one]
      nlinarith [sq_nonneg t]
    · have hone_t : 1 <= t := le_of_not_ge ht_one
      rw [max_eq_right hone_t]
      nlinarith [sq_nonneg t]
  change (t ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ <=
    5 * (positiveOrdinateZetaZeroClampedHeight rho ^ 2 +
      (1 / 2 : Real) ^ 2)⁻¹
  calc
    (t ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ =
        1 / (t ^ 2 + (1 / 2 : Real) ^ 2) := by simp
    _ <= 5 / (positiveOrdinateZetaZeroClampedHeight rho ^ 2 +
        (1 / 2 : Real) ^ 2) :=
      (div_le_div_iff₀ ha hb).2 (by simpa using hden)
    _ = 5 * (positiveOrdinateZetaZeroClampedHeight rho ^ 2 +
        (1 / 2 : Real) ^ 2)⁻¹ := by simp [div_eq_mul_inv]

/--
An exact actual-zero count and a cumulative dyadic `T log T` estimate imply
inverse-square summability over all positive-ordinate zeta zeroes.  No lower
bound for the first positive ordinate is required.
-/
theorem positiveOrdinateZetaZero_heightDecay_summable_of_exactCount_noLowerBound
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (C : Real) (hC_nonneg : 0 <= C)
    (hcount :
      forall m : Nat,
        heightCount ((2 : Real) ^ (m + 1)) <=
          C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1)))) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  let fiber : Nat -> Type := fun m =>
    PositiveOrdinateZetaZeroClampedDyadicShell m
  let fiberFintype : forall m : Nat, Fintype (fiber m) := fun m =>
    positiveOrdinateZetaZeroClampedDyadicShellFintype exactWindow m
  let height : Sigma fiber -> Real := fun p =>
    positiveOrdinateZetaZeroClampedHeight p.2.1
  let multiplicity : Sigma fiber -> Real := fun _p => 1
  let shellMass : Nat -> Real := fun m => ∑' _rho : fiber m, (1 : Real)
  let cumulativeMass : Nat -> Real := fun m =>
    heightCount ((2 : Real) ^ (m + 1))
  have hshell_le_cumulative :
      forall m : Nat, shellMass m <= cumulativeMass m := by
    intro m
    letI : Fintype (fiber m) := fiberFintype m
    have hcard :
        Fintype.card (fiber m) <=
          Fintype.card
            {rho : ZetaZeroSubtype //
              rho ∈ exactWindow.window ((2 : Real) ^ (m + 1))} :=
      Fintype.card_le_of_injective
        (positiveOrdinateZetaZeroClampedDyadicShellEmbedding exactWindow m)
        (positiveOrdinateZetaZeroClampedDyadicShellEmbedding exactWindow m).injective
    rw [show shellMass m = (Fintype.card (fiber m) : Real) by
      simp [shellMass]]
    change (Fintype.card (fiber m) : Real) <=
      heightCount ((2 : Real) ^ (m + 1))
    rw [exactWindow.heightCount_eq_card]
    have hcard' :
        Fintype.card (fiber m) <=
          (exactWindow.window ((2 : Real) ^ (m + 1))).card := by
      simpa using hcard
    exact_mod_cast hcard'
  have hsigma :
      Summable (fun p : Sigma fiber =>
        multiplicity p *
          (height p ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
    apply criticalLineShellHeightDecay_summable_of_cumulativeDyadicTlogTBound
      height multiplicity fiberFintype shellMass cumulativeMass C
    · intro p
      simp [multiplicity]
    · intro p
      have hpos : 0 < height p := by
        simp [height, positiveOrdinateZetaZeroClampedHeight]
      simpa [height, fiber, abs_of_pos hpos, p.2.2] using
        positiveOrdinateZetaZeroClampedDyadicShellIndex_lower p.2.1
    · intro m
      rfl
    · exact hC_nonneg
    · exact hshell_le_cumulative
    · exact hcount
  let shellEquiv : Sigma fiber ≃ PositiveOrdinateZetaZeroSubtype :=
    Equiv.sigmaFiberEquiv positiveOrdinateZetaZeroClampedDyadicShellIndex
  have hclamped :
      Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
        (positiveOrdinateZetaZeroClampedHeight rho ^ 2 +
          (1 / 2 : Real) ^ 2)⁻¹) := by
    apply shellEquiv.summable_iff.mp
    refine hsigma.congr ?_
    rintro ⟨m, rho⟩
    simp [multiplicity, height, shellEquiv, fiber, Function.comp_apply]
  have hfive := Summable.mul_left (5 : Real) hclamped
  exact Summable.of_nonneg_of_le
    (fun _rho => by positivity)
    positiveOrdinateZetaZero_heightDecay_le_five_mul_clamped
    hfive

namespace BellottiWongPublishedExactNTTheorem

/-- The exact Bellotti-Wong estimate gives a dyadic bound without a low-zero hypothesis. -/
theorem heightCount_dyadic_le_noZeroFree
    (source : BellottiWongPublishedExactNTTheorem)
    (m : Nat) :
    source.heightCount ((2 : Real) ^ (m + 1)) <=
      (20 + source.heightCount 2) *
        (((m : Real) + 2) * ((2 : Real) ^ (m + 1))) := by
  have hcount_two_nonneg : 0 <= source.heightCount 2 := by
    rw [source.exactHeightWindow.heightCount_eq_card]
    positivity
  by_cases hm : m = 0
  · subst m
    norm_num
    linarith
  · have hm_one : 1 <= m := Nat.one_le_iff_ne_zero.mpr hm
    have hvalid :
        bellottiWongValidFrom <= (2 : Real) ^ (m + 1) := by
      calc
        bellottiWongValidFrom <= 3 := by
          simpa [bellottiWongValidFrom] using Real.exp_one_lt_three.le
        _ <= 4 := by norm_num
        _ = (2 : Real) ^ 2 := by norm_num
        _ <= (2 : Real) ^ (m + 1) :=
          pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ hm_one)
    have habs := source.published_abs_error_le
      ((2 : Real) ^ (m + 1)) hvalid
    have hcount_le :
        source.heightCount ((2 : Real) ^ (m + 1)) <=
          riemannVonMangoldtMainTerm ((2 : Real) ^ (m + 1)) +
            bellottiWongErrorTerm ((2 : Real) ^ (m + 1)) := by
      have hupper := (abs_le.mp habs).2
      linarith
    have hmain := riemannVonMangoldtMainTerm_dyadic_le m
    have herror := bellottiWongErrorTerm_dyadic_le m
    have hT_one : 1 <= (2 : Real) ^ (m + 1) := by
      calc
        (1 : Real) = 2 ^ 0 := by norm_num
        _ <= 2 ^ (m + 1) :=
          pow_le_pow_right₀ (by norm_num) (Nat.zero_le (m + 1))
    have hm_two_nonneg : 0 <= (m : Real) + 2 := by positivity
    have herror_scaled :
        10 * ((m : Real) + 2) <=
          10 * ((m : Real) + 2) * ((2 : Real) ^ (m + 1)) := by
      have hfactor_nonneg : 0 <= (10 : Real) * ((m : Real) + 2) :=
        mul_nonneg (by norm_num) hm_two_nonneg
      have hscaled := mul_le_mul_of_nonneg_left hT_one
        hfactor_nonneg
      simpa using hscaled
    have htwenty :
        source.heightCount ((2 : Real) ^ (m + 1)) <=
          20 * (((m : Real) + 2) * ((2 : Real) ^ (m + 1))) := by
      calc
        source.heightCount ((2 : Real) ^ (m + 1)) <=
            riemannVonMangoldtMainTerm ((2 : Real) ^ (m + 1)) +
              bellottiWongErrorTerm ((2 : Real) ^ (m + 1)) := hcount_le
        _ <= 2 * (((m : Real) + 1) * ((2 : Real) ^ (m + 1))) +
            10 * ((m : Real) + 2) := add_le_add hmain herror
        _ <= 2 * (((m : Real) + 1) * ((2 : Real) ^ (m + 1))) +
            10 * ((m : Real) + 2) * ((2 : Real) ^ (m + 1)) :=
          add_le_add le_rfl herror_scaled
        _ <= 20 * (((m : Real) + 2) * ((2 : Real) ^ (m + 1))) := by
          have hpow_nonneg : 0 <= (2 : Real) ^ (m + 1) := by positivity
          nlinarith
    have hfactor_nonneg :
        0 <= ((m : Real) + 2) * ((2 : Real) ^ (m + 1)) := by positivity
    exact htwenty.trans (by nlinarith)

/--
Bellotti-Wong's numerical estimate implies actual positive-zero inverse-square
summability, with no separate zero-free interval assumption.
-/
theorem positiveOrdinateZetaZero_heightDecay_summable_noZeroFree
    (source : BellottiWongPublishedExactNTTheorem) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  apply positiveOrdinateZetaZero_heightDecay_summable_of_exactCount_noLowerBound
    source.exactHeightWindow (20 + source.heightCount 2)
  · have hcount_two_nonneg : 0 <= source.heightCount 2 := by
      rw [source.exactHeightWindow.heightCount_eq_card]
      positivity
    linarith
  · exact source.heightCount_dyadic_le_noZeroFree

/-- The same no-low-zero argument controls both conjugate nonreal halves. -/
theorem positiveNegativeOrdinateZetaZero_heightDecay_summable_noZeroFree
    (source : BellottiWongPublishedExactNTTheorem) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) ∧
      Summable (fun rho : NegativeOrdinateZetaZeroSubtype =>
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  have hpositive := source.positiveOrdinateZetaZero_heightDecay_summable_noZeroFree
  exact ⟨hpositive,
    negativeOrdinateZetaZero_heightDecay_summable_of_positive hpositive⟩

/--
For each fixed coefficient index, the Bellotti-Wong estimate controls the
actual unit-multiplicity positive-zero Li series without a low-zero hypothesis.
-/
theorem positiveOrdinateZetaZero_liSummand_summable_noZeroFree
    (source : BellottiWongPublishedExactNTTheorem)
    (n : Nat)
    (hcritical :
      forall rho : PositiveOrdinateZetaZeroSubtype,
        IsCriticalLine (rho : Complex)) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroLiSummand rho.1 n) := by
  have hdecay := source.positiveOrdinateZetaZero_heightDecay_summable_noZeroFree
  let majorant : PositiveOrdinateZetaZeroSubtype -> Real := fun rho =>
    ((n : Real) ^ 2 / 2) *
      (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹
  have hmajorant : Summable majorant := by
    simpa [majorant] using Summable.mul_left ((n : Real) ^ 2 / 2) hdecay
  exact
    @Summable.of_nonneg_of_le PositiveOrdinateZetaZeroSubtype majorant
      (fun rho => zetaZeroLiSummand rho.1 n)
      (fun rho => by
        rw [zetaZeroLiSummand_eq_criticalLineLiSummand rho.1 n (hcritical rho)]
        exact criticalLineLiSummand_nonneg (Complex.im (rho : Complex)) n)
      (fun rho => by
        rw [zetaZeroLiSummand_eq_criticalLineLiSummand rho.1 n (hcritical rho)]
        exact criticalLineLiSummand_le_quadratic_height_decay
          (Complex.im (rho : Complex)) n)
      hmajorant

/-- The resulting actual positive-zero Li coefficient is summable and nonnegative. -/
theorem positiveOrdinateZetaZeroLiCoefficient_summable_and_nonneg_noZeroFree
    (source : BellottiWongPublishedExactNTTheorem)
    (n : Nat)
    (hcritical :
      forall rho : PositiveOrdinateZetaZeroSubtype,
        IsCriticalLine (rho : Complex)) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
        zetaZeroLiSummand rho.1 n) ∧
      0 <= positiveOrdinateZetaZeroLiCoefficient n :=
  ⟨source.positiveOrdinateZetaZero_liSummand_summable_noZeroFree n hcritical,
    positiveOrdinateZetaZeroLiCoefficient_nonneg n hcritical⟩

end BellottiWongPublishedExactNTTheorem

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
