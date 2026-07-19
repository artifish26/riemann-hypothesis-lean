import RiemannHypothesisProject.LiCriterion.DyadicShells
import RiemannHypothesisProject.RiemannVonMangoldtClassicalCounting
import RiemannHypothesisProject.RiemannVonMangoldtConcretePublishedSources

/-!
# Actual zeta-zero height-decay summability

This module instantiates the dyadic Li shell argument on Mathlib's actual zeta
zero subtype.  An exact positive-ordinate height count supplies finite windows,
a lower bound above height `1` gives a canonical dyadic shell for every
positive-ordinate zero, and a cumulative `T log T` bound gives inverse-square
height-decay summability.

The source hypotheses remain visible: this is the zero-enumeration and shell
interpretation theorem, not a replacement for the external `N(T)` theorem or
the verified lower bound for the first positive ordinate.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open ComplexConjugate

/-- The subtype of actual zeta zeroes with strictly positive ordinate. -/
abbrev PositiveOrdinateZetaZeroSubtype :=
  {rho : ZetaZeroSubtype // 0 < Complex.im (rho : Complex)}

/-- The subtype of actual zeta zeroes with strictly negative ordinate. -/
abbrev NegativeOrdinateZetaZeroSubtype :=
  {rho : ZetaZeroSubtype // Complex.im (rho : Complex) < 0}

/-- Complex conjugation pairs the actual positive- and negative-ordinate zeta zeroes. -/
noncomputable def positiveNegativeOrdinateZetaZeroConjEquiv :
    PositiveOrdinateZetaZeroSubtype ≃ NegativeOrdinateZetaZeroSubtype where
  toFun rho :=
    ⟨⟨conj (rho : Complex),
        zetaZeroConjugationSymmetry (rho : Complex) rho.1.property⟩, by
      simpa using neg_lt_zero.mpr rho.2⟩
  invFun rho :=
    ⟨⟨conj (rho : Complex),
        zetaZeroConjugationSymmetry (rho : Complex) rho.1.property⟩, by
      simpa using neg_pos.mpr rho.2⟩
  left_inv rho := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv rho := by
    apply Subtype.ext
    apply Subtype.ext
    simp

/-- Conjugation negates the ordinate in the actual positive-to-negative pairing. -/
theorem positiveNegativeOrdinateZetaZeroConjEquiv_im
    (rho : PositiveOrdinateZetaZeroSubtype) :
    Complex.im (positiveNegativeOrdinateZetaZeroConjEquiv rho : Complex) =
      -Complex.im (rho : Complex) := by
  simp [positiveNegativeOrdinateZetaZeroConjEquiv]

/--
The canonical dyadic shell index of a real height.  Heights below `1` are sent
to shell zero; the source theorem below uses this only when the height is at
least `1`.
-/
noncomputable def realDyadicShellIndex (t : Real) : Nat :=
  if ht : 1 <= t then
    Classical.choose
      (exists_nat_pow_near ht (by norm_num : (1 : Real) < 2))
  else
    0

/-- A height at least `1` lies above the lower edge of its canonical dyadic shell. -/
theorem realDyadicShellIndex_lower {t : Real} (ht : 1 <= t) :
    (2 : Real) ^ realDyadicShellIndex t <= t := by
  rw [realDyadicShellIndex, dif_pos ht]
  exact
    (Classical.choose_spec
      (exists_nat_pow_near ht (by norm_num : (1 : Real) < 2))).1

/-- A height at least `1` lies below the upper edge of its canonical dyadic shell. -/
theorem realDyadicShellIndex_lt_upper {t : Real} (ht : 1 <= t) :
    t < (2 : Real) ^ (realDyadicShellIndex t + 1) := by
  rw [realDyadicShellIndex, dif_pos ht]
  exact
    (Classical.choose_spec
      (exists_nat_pow_near ht (by norm_num : (1 : Real) < 2))).2

/-- The canonical dyadic shell index of an actual positive-ordinate zeta zero. -/
noncomputable def positiveOrdinateZetaZeroDyadicShellIndex
    (rho : PositiveOrdinateZetaZeroSubtype) : Nat :=
  realDyadicShellIndex (Complex.im (rho : Complex))

/-- The actual positive-ordinate zeta zeroes assigned to dyadic shell `m`. -/
abbrev PositiveOrdinateZetaZeroDyadicShell (m : Nat) :=
  {rho : PositiveOrdinateZetaZeroSubtype //
    positiveOrdinateZetaZeroDyadicShellIndex rho = m}

/--
Under a verified lower bound above `1`, every actual positive-ordinate zeta
zero lies above the lower edge of its canonical dyadic shell.
-/
theorem positiveOrdinateZetaZeroDyadicShellIndex_lower
    (hlower : PositiveOrdinateZetaZeroLowerBound 1)
    (rho : PositiveOrdinateZetaZeroSubtype) :
    (2 : Real) ^ positiveOrdinateZetaZeroDyadicShellIndex rho <=
      Complex.im (rho : Complex) := by
  exact realDyadicShellIndex_lower (le_of_lt (hlower rho.1 rho.2))

/--
Under the same lower bound, every actual positive-ordinate zeta zero lies below
the upper edge of its canonical dyadic shell.
-/
theorem positiveOrdinateZetaZeroDyadicShellIndex_lt_upper
    (hlower : PositiveOrdinateZetaZeroLowerBound 1)
    (rho : PositiveOrdinateZetaZeroSubtype) :
    Complex.im (rho : Complex) <
      (2 : Real) ^ (positiveOrdinateZetaZeroDyadicShellIndex rho + 1) := by
  exact realDyadicShellIndex_lt_upper (le_of_lt (hlower rho.1 rho.2))

/--
Each actual dyadic shell embeds into the exact positive-ordinate height window
at its upper endpoint.
-/
noncomputable def positiveOrdinateZetaZeroDyadicShellEmbedding
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (hlower : PositiveOrdinateZetaZeroLowerBound 1)
    (m : Nat) :
    PositiveOrdinateZetaZeroDyadicShell m ↪
      {rho : ZetaZeroSubtype //
        rho ∈ exactWindow.window ((2 : Real) ^ (m + 1))} where
  toFun rho := by
    refine ⟨rho.1.1, (exactWindow.mem_window_iff _ rho.1.1).mpr ⟨rho.1.2, ?_⟩⟩
    have hupper :=
      positiveOrdinateZetaZeroDyadicShellIndex_lt_upper hlower rho.1
    simpa [rho.2] using hupper.le
  inj' := by
    intro rho sigma h
    have hzeta : rho.1.1 = sigma.1.1 :=
      congrArg (fun z => z.1) h
    exact Subtype.ext (Subtype.ext hzeta)

/-- The exact positive-ordinate height window makes every actual dyadic shell finite. -/
@[reducible] noncomputable def positiveOrdinateZetaZeroDyadicShellFintype
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (hlower : PositiveOrdinateZetaZeroLowerBound 1)
    (m : Nat) :
    Fintype (PositiveOrdinateZetaZeroDyadicShell m) := by
  letI : Finite (PositiveOrdinateZetaZeroDyadicShell m) :=
    Finite.of_injective
      (positiveOrdinateZetaZeroDyadicShellEmbedding exactWindow hlower m)
      (positiveOrdinateZetaZeroDyadicShellEmbedding exactWindow hlower m).injective
  exact Fintype.ofFinite _

/--
An exact actual-zeta `N(T)` window, a verified first-ordinate lower bound, and a
dyadic cumulative `T log T` estimate imply inverse-square summability over all
actual positive-ordinate zeta zeroes.

This is the source theorem that instantiates the abstract shell fibers used by
the critical-line Li summability argument.
-/
theorem positiveOrdinateZetaZero_heightDecay_summable_of_exactCount
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (hlower : PositiveOrdinateZetaZeroLowerBound 1)
    (C : Real) (hC_nonneg : 0 <= C)
    (hcount :
      forall m : Nat,
        heightCount ((2 : Real) ^ (m + 1)) <=
          C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1)))) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  let fiber : Nat -> Type := fun m => PositiveOrdinateZetaZeroDyadicShell m
  let fiberFintype : forall m : Nat, Fintype (fiber m) := fun m =>
    positiveOrdinateZetaZeroDyadicShellFintype exactWindow hlower m
  let height : Sigma fiber -> Real := fun p => Complex.im (p.2.1 : Complex)
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
        (positiveOrdinateZetaZeroDyadicShellEmbedding exactWindow hlower m)
        (positiveOrdinateZetaZeroDyadicShellEmbedding exactWindow hlower m).injective
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
      have hpos : 0 < Complex.im (p.2.1 : Complex) := p.2.1.2
      simpa [height, fiber, abs_of_pos hpos, p.2.2] using
        positiveOrdinateZetaZeroDyadicShellIndex_lower hlower p.2.1
    · intro m
      rfl
    · exact hC_nonneg
    · exact hshell_le_cumulative
    · intro m
      exact hcount m
  let shellEquiv : Sigma fiber ≃ PositiveOrdinateZetaZeroSubtype :=
    Equiv.sigmaFiberEquiv positiveOrdinateZetaZeroDyadicShellIndex
  have hsigma' :
      Summable (fun p : Sigma fiber =>
        (Complex.im (shellEquiv p : Complex) ^ 2 +
          (1 / 2 : Real) ^ 2)⁻¹) := by
    simpa [height, multiplicity, shellEquiv, fiber] using hsigma
  exact shellEquiv.summable_iff.mp hsigma'

/--
Conjugation transports inverse-square height-decay summability from the actual
positive-ordinate zeta zeroes to the actual negative-ordinate zeroes.
-/
theorem negativeOrdinateZetaZero_heightDecay_summable_of_positive
    (hpositive :
      Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹)) :
    Summable (fun rho : NegativeOrdinateZetaZeroSubtype =>
      (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  let e := positiveNegativeOrdinateZetaZeroConjEquiv
  apply e.summable_iff.mp
  refine hpositive.congr ?_
  intro rho
  simp [e, positiveNegativeOrdinateZetaZeroConjEquiv, pow_two]

/--
The exact-count source theorem supplies inverse-square summability on both
halves of the actual nonreal zeta-zero set.
-/
theorem positiveNegativeOrdinateZetaZero_heightDecay_summable_of_exactCount
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (hlower : PositiveOrdinateZetaZeroLowerBound 1)
    (C : Real) (hC_nonneg : 0 <= C)
    (hcount :
      forall m : Nat,
        heightCount ((2 : Real) ^ (m + 1)) <=
          C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1)))) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) ∧
      Summable (fun rho : NegativeOrdinateZetaZeroSubtype =>
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  have hpositive :=
    positiveOrdinateZetaZero_heightDecay_summable_of_exactCount
      exactWindow hlower C hC_nonneg hcount
  exact
    ⟨hpositive,
      negativeOrdinateZetaZero_heightDecay_summable_of_positive hpositive⟩

/-- The classical Li summand attached directly to an actual zeta zero. -/
noncomputable def zetaZeroLiSummand (rho : ZetaZeroSubtype) (n : Nat) : Real :=
  (1 - (1 - (rho : Complex)⁻¹) ^ n).re

/-- A point on the critical line is the critical-line point at its own ordinate. -/
theorem eq_criticalLinePoint_im_of_isCriticalLine
    {z : Complex} (hz : IsCriticalLine z) :
    z = criticalLinePoint (Complex.im z) := by
  apply Complex.ext
  · simpa [IsCriticalLine, criticalLinePoint] using hz
  · simp [criticalLinePoint]

/-- On the critical line, the actual zeta-zero Li summand is the checked height summand. -/
theorem zetaZeroLiSummand_eq_criticalLineLiSummand
    (rho : ZetaZeroSubtype) (n : Nat)
    (hcritical : IsCriticalLine (rho : Complex)) :
    zetaZeroLiSummand rho n =
      criticalLineLiSummand (Complex.im (rho : Complex)) n := by
  have hrho := eq_criticalLinePoint_im_of_isCriticalLine hcritical
  unfold zetaZeroLiSummand
  conv_lhs => rw [hrho]
  rfl

/--
The unit-multiplicity positive-ordinate zeta Li series is summable once the
actual exact count supplies inverse-square height decay and the relevant zeroes
are known to lie on the critical line.
-/
theorem positiveOrdinateZetaZero_liSummand_summable_of_exactCount
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (hlower : PositiveOrdinateZetaZeroLowerBound 1)
    (C : Real) (hC_nonneg : 0 <= C)
    (hcount :
      forall m : Nat,
        heightCount ((2 : Real) ^ (m + 1)) <=
          C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1))))
    (n : Nat)
    (hcritical :
      forall rho : PositiveOrdinateZetaZeroSubtype,
        IsCriticalLine (rho : Complex)) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroLiSummand rho.1 n) := by
  have hdecay :=
    positiveOrdinateZetaZero_heightDecay_summable_of_exactCount
      exactWindow hlower C hC_nonneg hcount
  let majorant : PositiveOrdinateZetaZeroSubtype -> Real := fun rho =>
    ((n : Real) ^ 2 / 2) *
      (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹
  have hmajorant : Summable majorant := by
    simpa [majorant] using
      Summable.mul_left ((n : Real) ^ 2 / 2) hdecay
  exact
    @Summable.of_nonneg_of_le PositiveOrdinateZetaZeroSubtype majorant
      (fun rho => zetaZeroLiSummand rho.1 n)
      (fun rho => by
        rw [zetaZeroLiSummand_eq_criticalLineLiSummand rho.1 n (hcritical rho)]
        exact criticalLineLiSummand_nonneg (Complex.im (rho : Complex)) n)
      (fun rho => by
        rw [zetaZeroLiSummand_eq_criticalLineLiSummand rho.1 n (hcritical rho)]
        exact
          criticalLineLiSummand_le_quadratic_height_decay
            (Complex.im (rho : Complex)) n)
      hmajorant

/-- The positive-ordinate, unit-multiplicity actual zeta Li coefficient. -/
noncomputable def positiveOrdinateZetaZeroLiCoefficient (n : Nat) : Real :=
  ∑' rho : PositiveOrdinateZetaZeroSubtype, zetaZeroLiSummand rho.1 n

/--
The actual positive-ordinate zeta Li coefficient is nonnegative when those
zeroes lie on the critical line.
-/
theorem positiveOrdinateZetaZeroLiCoefficient_nonneg
    (n : Nat)
    (hcritical :
      forall rho : PositiveOrdinateZetaZeroSubtype,
        IsCriticalLine (rho : Complex)) :
    0 <= positiveOrdinateZetaZeroLiCoefficient n := by
  unfold positiveOrdinateZetaZeroLiCoefficient
  exact tsum_nonneg (fun rho => by
    rw [zetaZeroLiSummand_eq_criticalLineLiSummand rho.1 n (hcritical rho)]
    exact criticalLineLiSummand_nonneg (Complex.im (rho : Complex)) n)

/--
Exact actual-zeta counting and critical-line geometry give a summable,
nonnegative unit-multiplicity positive-ordinate Li coefficient.
-/
theorem positiveOrdinateZetaZeroLiCoefficient_summable_and_nonneg_of_exactCount
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (hlower : PositiveOrdinateZetaZeroLowerBound 1)
    (C : Real) (hC_nonneg : 0 <= C)
    (hcount :
      forall m : Nat,
        heightCount ((2 : Real) ^ (m + 1)) <=
          C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1))))
    (n : Nat)
    (hcritical :
      forall rho : PositiveOrdinateZetaZeroSubtype,
        IsCriticalLine (rho : Complex)) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
        zetaZeroLiSummand rho.1 n) ∧
      0 <= positiveOrdinateZetaZeroLiCoefficient n :=
  ⟨positiveOrdinateZetaZero_liSummand_summable_of_exactCount
      exactWindow hlower C hC_nonneg hcount n hcritical,
    positiveOrdinateZetaZeroLiCoefficient_nonneg n hcritical⟩

/-- The Riemann-von Mangoldt main term has the required dyadic `T log T` shape. -/
theorem riemannVonMangoldtMainTerm_dyadic_le
    (m : Nat) :
    riemannVonMangoldtMainTerm ((2 : Real) ^ (m + 1)) <=
      2 * (((m : Real) + 1) * ((2 : Real) ^ (m + 1))) := by
  let T : Real := (2 : Real) ^ (m + 1)
  have hT_pos : 0 < T := by positivity
  have hT_nonneg : 0 <= T := hT_pos.le
  have hT_ge_two : 2 <= T := by
    dsimp [T]
    calc
      (2 : Real) = 2 ^ 1 := by norm_num
      _ <= 2 ^ (m + 1) :=
        pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ (Nat.zero_le m))
  have hlogT_nonneg : 0 <= Real.log T :=
    Real.log_nonneg (by linarith)
  have hlog_two_le_two : Real.log 2 <= (2 : Real) :=
    Real.log_le_self (by norm_num)
  have hlogT_le : Real.log T <= 2 * ((m : Real) + 1) := by
    dsimp [T]
    rw [Real.log_pow]
    have hm_nonneg : 0 <= (m : Real) := Nat.cast_nonneg m
    have hscale_nonneg : 0 <= ((m + 1 : Nat) : Real) := by positivity
    have hscaled :=
      mul_le_mul_of_nonneg_left hlog_two_le_two hscale_nonneg
    norm_num [Nat.cast_add] at hscaled ⊢
    nlinarith
  have hden_pos : 0 < 2 * Real.pi * Real.exp 1 := by positivity
  have hden_one : 1 <= 2 * Real.pi * Real.exp 1 := by
    have htwoPi : 1 <= 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hexp : 1 <= Real.exp 1 := Real.one_le_exp zero_le_one
    nlinarith
  have hratio_pos : 0 < T / (2 * Real.pi * Real.exp 1) := by positivity
  have hratio_le_T : T / (2 * Real.pi * Real.exp 1) <= T := by
    rw [div_le_iff₀ hden_pos]
    nlinarith [mul_le_mul_of_nonneg_left hden_one hT_nonneg]
  have hlog_ratio_le :
      Real.log (T / (2 * Real.pi * Real.exp 1)) <= Real.log T :=
    Real.log_le_log hratio_pos hratio_le_T
  have hcoef_nonneg : 0 <= T / (2 * Real.pi) := by positivity
  have hcoef_le_T : T / (2 * Real.pi) <= T := by
    have htwoPi_pos : 0 < 2 * Real.pi := by positivity
    have htwoPi_one : 1 <= 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    rw [div_le_iff₀ htwoPi_pos]
    nlinarith [mul_le_mul_of_nonneg_left htwoPi_one hT_nonneg]
  have hmain_le :
      T / (2 * Real.pi) *
          Real.log (T / (2 * Real.pi * Real.exp 1)) <=
        T * (2 * ((m : Real) + 1)) := by
    exact
      (mul_le_mul_of_nonneg_left hlog_ratio_le hcoef_nonneg).trans
        (mul_le_mul hcoef_le_T hlogT_le hlogT_nonneg hT_nonneg)
  dsimp [riemannVonMangoldtMainTerm]
  change T / (2 * Real.pi) *
      Real.log (T / (2 * Real.pi * Real.exp 1)) <=
    2 * (((m : Real) + 1) * T)
  nlinarith

/-- The Bellotti-Wong error term is smaller than a linear dyadic shell factor. -/
theorem bellottiWongErrorTerm_dyadic_le
    (m : Nat) :
    bellottiWongErrorTerm ((2 : Real) ^ (m + 1)) <=
      10 * ((m : Real) + 2) := by
  let T : Real := (2 : Real) ^ (m + 1)
  have hT_ge_two : 2 <= T := by
    dsimp [T]
    calc
      (2 : Real) = 2 ^ 1 := by norm_num
      _ <= 2 ^ (m + 1) :=
        pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ (Nat.zero_le m))
  have hlogT_nonneg : 0 <= Real.log T :=
    Real.log_nonneg (by linarith)
  have hlogT_le : Real.log T <= 2 * ((m : Real) + 1) := by
    dsimp [T]
    rw [Real.log_pow]
    have hlog_two_le_two : Real.log 2 <= (2 : Real) :=
      Real.log_le_self (by norm_num)
    have hscale_nonneg : 0 <= ((m + 1 : Nat) : Real) := by positivity
    have hscaled :=
      mul_le_mul_of_nonneg_left hlog_two_le_two hscale_nonneg
    norm_num [Nat.cast_add] at hscaled ⊢
    nlinarith
  have hloglog_le : Real.log (Real.log T) <= Real.log T :=
    Real.log_le_self hlogT_nonneg
  have hfirst :
      ((10076 : Real) / 100000) * Real.log T <= Real.log T := by
    nlinarith
  have hsecond :
      ((24460 : Real) / 100000) * Real.log (Real.log T) <=
        Real.log T := by
    have hcoef_nonneg : (0 : Real) <= 24460 / 100000 := by norm_num
    have hscaled := mul_le_mul_of_nonneg_left hloglog_le hcoef_nonneg
    have hcoef_log_le :
        ((24460 : Real) / 100000) * Real.log T <= Real.log T := by
      nlinarith
    exact hscaled.trans hcoef_log_le
  have hm_nonneg : 0 <= (m : Real) := Nat.cast_nonneg m
  dsimp [bellottiWongErrorTerm]
  nlinarith

namespace BellottiWongPublishedExactNTTheorem

/--
The exact published Bellotti-Wong count has the cumulative dyadic `T log T`
bound required by the actual zeta-zero shell theorem.
-/
theorem heightCount_dyadic_le
    (source : BellottiWongPublishedExactNTTheorem)
    (hfree : ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (m : Nat) :
    source.heightCount ((2 : Real) ^ (m + 1)) <=
      20 * (((m : Real) + 2) * ((2 : Real) ^ (m + 1))) := by
  by_cases hm : m = 0
  · subst m
    have hzero : source.heightCount ((2 : Real) ^ (0 + 1)) = 0 :=
      source.heightCount_eq_zero_below_of_zetaZeroFreePositiveOrdinateBand
        hfree ((2 : Real) ^ (0 + 1)) (by
          simpa [bellottiWongValidFrom] using Real.exp_one_gt_two)
    rw [hzero]
    norm_num
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

/--
The exact Bellotti-Wong source theorem and its zero-free band discharge every
hypothesis of the actual positive-ordinate zeta height-decay theorem.
-/
theorem positiveOrdinateZetaZero_heightDecay_summable
    (source : BellottiWongPublishedExactNTTheorem)
    (hfree : ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  have hlower_e :=
    positiveOrdinateZetaZeroLowerBound_of_zetaZeroFreePositiveOrdinateBand hfree
  have hlower_one : PositiveOrdinateZetaZeroLowerBound 1 := by
    intro rho hpos
    exact (Real.one_lt_exp_iff.mpr zero_lt_one).trans (hlower_e rho hpos)
  exact positiveOrdinateZetaZero_heightDecay_summable_of_exactCount
    source.exactHeightWindow hlower_one 20 (by norm_num)
    (source.heightCount_dyadic_le hfree)

/--
The exact Bellotti-Wong source theorem gives inverse-square summability for the
actual conjugate positive/negative zeta-zero pair.
-/
theorem positiveNegativeOrdinateZetaZero_heightDecay_summable
    (source : BellottiWongPublishedExactNTTheorem)
    (hfree : ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) ∧
      Summable (fun rho : NegativeOrdinateZetaZeroSubtype =>
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  have hpositive := source.positiveOrdinateZetaZero_heightDecay_summable hfree
  exact
    ⟨hpositive,
      negativeOrdinateZetaZero_heightDecay_summable_of_positive hpositive⟩

/--
The Bellotti-Wong exact source gives the actual unit-multiplicity positive-zero
Li coefficient theorem under the explicit critical-line hypothesis.
-/
theorem positiveOrdinateZetaZeroLiCoefficient_summable_and_nonneg
    (source : BellottiWongPublishedExactNTTheorem)
    (hfree : ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (n : Nat)
    (hcritical :
      forall rho : PositiveOrdinateZetaZeroSubtype,
        IsCriticalLine (rho : Complex)) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
        zetaZeroLiSummand rho.1 n) ∧
      0 <= positiveOrdinateZetaZeroLiCoefficient n := by
  have hlower_e :=
    positiveOrdinateZetaZeroLowerBound_of_zetaZeroFreePositiveOrdinateBand hfree
  have hlower_one : PositiveOrdinateZetaZeroLowerBound 1 := by
    intro rho hpos
    exact (Real.one_lt_exp_iff.mpr zero_lt_one).trans (hlower_e rho hpos)
  exact positiveOrdinateZetaZeroLiCoefficient_summable_and_nonneg_of_exactCount
    source.exactHeightWindow hlower_one 20 (by norm_num)
    (source.heightCount_dyadic_le hfree) n hcritical

end BellottiWongPublishedExactNTTheorem

end ComplexCompactExhaustion

end RiemannHypothesisProject
