import RiemannHypothesisProject.GuinandWeilConcrete.XiFiniteBlaschkeRemoval
import RiemannHypothesisProject.GuinandWeilConcrete.XiGoodHeightSelection

/-!
# Local xi bounds at canonical good heights

This module compares the exact radius-four xi divisor disk around `3 + iT`
with the canonical positive-ordinate zeta-zero window.  It then combines the
selected-height separation with the finite Blaschke residual estimate.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Complex Metric Set

noncomputable section

/-- The exact local xi-zero subtype in the radius-four disk at height `T`. -/
def XiGoodHeightLocalZeroSubtype (T : Real) :=
  {u : Complex //
    u ∈ shiftedRiemannXiOpenBallZeroFinset (xiLocalDiskCenter T) 4}

/-- A local translated xi zero, returned to its global zeta-zero coordinate. -/
noncomputable def xiGoodHeightLocalZetaZero
    (T : Real) (u : XiGoodHeightLocalZeroSubtype T) : ZetaZeroSubtype :=
  zetaZeroSubtypeOfRiemannXiZero (xiLocalDiskCenter T + u.1) (by
    have hu :=
      (mem_shiftedRiemannXiOpenBallZeroFinset_iff.mp u.2).2
    simpa only [shiftedRiemannXi] using hu)

@[simp]
theorem coe_xiGoodHeightLocalZetaZero
    (T : Real) (u : XiGoodHeightLocalZeroSubtype T) :
    (xiGoodHeightLocalZetaZero T u : Complex) =
      xiLocalDiskCenter T + u.1 := rfl

theorem xiGoodHeightLocalZetaZero_injective (T : Real) :
    Function.Injective (xiGoodHeightLocalZetaZero T) := by
  intro u v huv
  apply Subtype.ext
  have hvalue := congrArg (fun rho : ZetaZeroSubtype => (rho : Complex)) huv
  change xiLocalDiskCenter T + u.1 = xiLocalDiskCenter T + v.1 at hvalue
  exact add_left_cancel hvalue

/-- For `T` in the selected unit interval, every radius-four local xi zero is
positive and lies below the padded canonical cutoff `N + 5`. -/
theorem xiGoodHeightLocalZetaZero_mem_canonicalWindow
    {N : Nat} (hN : 5 ≤ N) {T : Real}
    (hTN : (N : Real) ≤ T) (hTN1 : T ≤ N + 1)
    (u : XiGoodHeightLocalZeroSubtype T) :
    xiGoodHeightLocalZetaZero T u ∈
      canonicalExactPositiveOrdinateZetaZeroWindow.window (N + 5) := by
  have huBall :=
    (mem_shiftedRiemannXiOpenBallZeroFinset_iff.mp u.2).1
  have huNorm : norm u.1 < 4 := by
    simpa [mem_ball, dist_zero_right] using huBall
  have huImAbs : abs u.1.im < 4 :=
    (Complex.abs_im_le_norm u.1).trans_lt huNorm
  have huImLower : -4 < u.1.im := (abs_lt.mp huImAbs).1
  have huImUpper : u.1.im < 4 := (abs_lt.mp huImAbs).2
  apply
    (canonicalExactPositiveOrdinateZetaZeroWindow.mem_window_iff
      (N + 5) (xiGoodHeightLocalZetaZero T u)).mpr
  have hcenterIm : (xiLocalDiskCenter T).im = T := by
    norm_num [xiLocalDiskCenter]
  constructor
  · rw [coe_xiGoodHeightLocalZetaZero, Complex.add_im, hcenterIm]
    have hNreal : (5 : Real) ≤ N := by exact_mod_cast hN
    linarith
  · rw [coe_xiGoodHeightLocalZetaZero, Complex.add_im, hcenterIm]
    linarith

/-- The global zeta-zero image of the exact local divisor disk. -/
noncomputable def xiGoodHeightLocalZetaZeroFinset (T : Real) :
    Finset ZetaZeroSubtype :=
  (shiftedRiemannXiOpenBallZeroFinset (xiLocalDiskCenter T) 4).attach.image
    (xiGoodHeightLocalZetaZero T)

theorem xiGoodHeightLocalZetaZeroFinset_subset_canonicalWindow
    {N : Nat} (hN : 5 ≤ N) {T : Real}
    (hTN : (N : Real) ≤ T) (hTN1 : T ≤ N + 1) :
    xiGoodHeightLocalZetaZeroFinset T ⊆
      canonicalExactPositiveOrdinateZetaZeroWindow.window (N + 5) := by
  intro rho hrho
  rw [xiGoodHeightLocalZetaZeroFinset, Finset.mem_image] at hrho
  obtain ⟨u, _hu, rfl⟩ := hrho
  exact xiGoodHeightLocalZetaZero_mem_canonicalWindow hN hTN hTN1 u

/-- The total analytic multiplicity in the radius-four local xi disk is at
most the canonical positive-ordinate multiplicity count below `N + 5`. -/
theorem sum_shiftedRiemannXiMultiplicity_localDisk_le_canonicalCount
    {N : Nat} (hN : 5 ≤ N) {T : Real}
    (hTN : (N : Real) ≤ T) (hTN1 : T ≤ N + 1) :
    (∑ u ∈ shiftedRiemannXiOpenBallZeroFinset (xiLocalDiskCenter T) 4,
        (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Real)) ≤
      canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) := by
  have hsum_eq :
      (∑ u ∈ shiftedRiemannXiOpenBallZeroFinset (xiLocalDiskCenter T) 4,
          (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Real)) =
        ∑ rho ∈ xiGoodHeightLocalZetaZeroFinset T,
          zetaZeroMultiplicityReal rho := by
    rw [xiGoodHeightLocalZetaZeroFinset, Finset.sum_image]
    · rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro u _hu
      unfold zetaZeroMultiplicityReal
      have hzero :=
        (mem_shiftedRiemannXiOpenBallZeroFinset_iff.mp u.2).2
      have hmult := shiftedRiemannXiMultiplicity_eq_zetaZeroMultiplicity
        (xiLocalDiskCenter T) u.1 hzero
      have hrho :
          zetaZeroSubtypeOfRiemannXiZero (xiLocalDiskCenter T + u.1) (by
            simpa only [shiftedRiemannXi] using hzero) =
            xiGoodHeightLocalZetaZero T u := by
        apply Subtype.ext
        rfl
      rw [hmult, hrho]
    · intro a _ha b _hb hab
      exact xiGoodHeightLocalZetaZero_injective T hab
  have hsubset : xiGoodHeightLocalZetaZeroFinset T ⊆
      canonicalExactPositiveOrdinateZetaZeroWindow.window (N + 5) := by
    exact xiGoodHeightLocalZetaZeroFinset_subset_canonicalWindow hN hTN hTN1
  have hsum_le :
      (∑ rho ∈ xiGoodHeightLocalZetaZeroFinset T,
          zetaZeroMultiplicityReal rho) ≤
        ∑ rho ∈ canonicalExactPositiveOrdinateZetaZeroWindow.window (N + 5),
          zetaZeroMultiplicityReal rho := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun rho _hrho _hnot => (zetaZeroMultiplicityReal_pos rho).le)
  rw [hsum_eq]
  calc
    (∑ rho ∈ xiGoodHeightLocalZetaZeroFinset T,
        zetaZeroMultiplicityReal rho) ≤
        ∑ rho ∈ canonicalExactPositiveOrdinateZetaZeroWindow.window (N + 5),
          zetaZeroMultiplicityReal rho := hsum_le
    _ = canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) := by
      unfold canonicalPositiveOrdinateZetaZeroMultiplicityCount
        multiplicityWeightedPositiveOrdinateHeightCountReal
      rw [← Finset.sum_attach]
      simp only [Finset.attach_eq_univ]

/-- Local coordinate of the horizontal contour point `sigma + iT` relative
to the disk center `3 + iT`. -/
def xiHorizontalLocalCoordinate (sigma : Real) : Complex :=
  (sigma - 3 : Real)

/-- The selected-height separation excludes every horizontal local coordinate
from the exact xi zero disk. -/
theorem xiHorizontalLocalCoordinate_not_mem_localZeroFinset
    {N : Nat} (hN : 5 ≤ N) {T : Real}
    (hTN : (N : Real) ≤ T) (hTN1 : T ≤ N + 1)
    (hsep : ∀ rho ∈
      canonicalExactPositiveOrdinateZetaZeroWindow.window (N + 5),
        1 /
            (4 *
              (canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) + 1)) <=
          |T - im (rho : Complex)|)
    (sigma : Real) :
    xiHorizontalLocalCoordinate sigma ∉
      shiftedRiemannXiOpenBallZeroFinset (xiLocalDiskCenter T) 4 := by
  intro hmem
  let u : XiGoodHeightLocalZeroSubtype T :=
    ⟨xiHorizontalLocalCoordinate sigma, hmem⟩
  have huWindow :=
    xiGoodHeightLocalZetaZero_mem_canonicalWindow hN hTN hTN1 u
  have h := hsep (xiGoodHeightLocalZetaZero T u) huWindow
  have hcountNonneg :
      0 <= canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) :=
    canonicalPositiveOrdinateZetaZeroMultiplicityCount_nonneg _
  have hleft :
      0 < 1 /
        (4 * (canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) + 1)) := by
    positivity
  have hzero :
      |T - im (xiGoodHeightLocalZetaZero T u : Complex)| = 0 := by
    simp [u, xiHorizontalLocalCoordinate, xiLocalDiskCenter]
  rw [hzero] at h
  linarith

/-- At a selected height, the exact radius-four xi principal-part sum has the
same quadratic multiplicity-count bound as the full canonical window. -/
theorem norm_xiLocalDisk_principalPart_le_canonicalCount
    {N : Nat} (hN : 5 ≤ N) {T : Real}
    (hTN : (N : Real) ≤ T) (hTN1 : T ≤ N + 1)
    (hsep : ∀ rho ∈
      canonicalExactPositiveOrdinateZetaZeroWindow.window (N + 5),
        1 /
            (4 *
              (canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) + 1)) <=
          |T - im (rho : Complex)|)
    (sigma : Real) :
    norm
        (∑ u ∈
            shiftedRiemannXiOpenBallZeroFinset (xiLocalDiskCenter T) 4,
          (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Complex) /
            (xiHorizontalLocalCoordinate sigma - u)) <=
      4 * canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) *
        (canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) + 1) := by
  let C := canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5)
  let localZeros :=
    shiftedRiemannXiOpenBallZeroFinset (xiLocalDiskCenter T) 4
  have hC : 0 <= C := by
    dsimp only [C]
    exact canonicalPositiveOrdinateZetaZeroMultiplicityCount_nonneg _
  have hcount :
      (∑ u ∈ localZeros,
          (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Real)) <= C := by
    dsimp only [localZeros, C]
    exact sum_shiftedRiemannXiMultiplicity_localDisk_le_canonicalCount
      hN hTN hTN1
  have hterm : ∀ u ∈ localZeros,
      norm
          ((shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Complex) /
            (xiHorizontalLocalCoordinate sigma - u)) <=
        (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Real) *
          (4 * (C + 1)) := by
    intro u hu
    let uSub : XiGoodHeightLocalZeroSubtype T := ⟨u, by simpa [localZeros] using hu⟩
    let rho := xiGoodHeightLocalZetaZero T uSub
    have hrhoWindow :=
      xiGoodHeightLocalZetaZero_mem_canonicalWindow hN hTN hTN1 uSub
    have hsepRho : 1 / (4 * (C + 1)) <= |T - im (rho : Complex)| := by
      simpa only [C, rho] using hsep rho hrhoWindow
    have himrho : im (rho : Complex) = T + im u := by
      dsimp only [rho]
      simp [uSub, xiLocalDiskCenter]
    have hsepIm : 1 / (4 * (C + 1)) <= |im u| := by
      rw [himrho] at hsepRho
      simpa only [sub_add_cancel_left, abs_neg] using hsepRho
    have himDenom : |im u| <= norm (xiHorizontalLocalCoordinate sigma - u) := by
      have h := Complex.abs_im_le_norm (xiHorizontalLocalCoordinate sigma - u)
      simpa [xiHorizontalLocalCoordinate] using h
    have hdelta : 1 / (4 * (C + 1)) <=
        norm (xiHorizontalLocalCoordinate sigma - u) := hsepIm.trans himDenom
    have hdeltaPos : 0 < 1 / (4 * (C + 1)) := by positivity
    have hdenomPos : 0 < norm (xiHorizontalLocalCoordinate sigma - u) :=
      hdeltaPos.trans_le hdelta
    rw [norm_div, norm_natCast]
    have hdiv :
        (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Real) /
            norm (xiHorizontalLocalCoordinate sigma - u) <=
          (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Real) /
            (1 / (4 * (C + 1))) := by
      exact div_le_div_of_nonneg_left (by positivity) hdeltaPos hdelta
    calc
      (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Real) /
          norm (xiHorizontalLocalCoordinate sigma - u) <=
        (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Real) /
          (1 / (4 * (C + 1))) := hdiv
      _ = (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Real) *
          (4 * (C + 1)) := by field_simp
  calc
    norm
        (∑ u ∈ localZeros,
          (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Complex) /
            (xiHorizontalLocalCoordinate sigma - u)) <=
      ∑ u ∈ localZeros,
        norm
          ((shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Complex) /
            (xiHorizontalLocalCoordinate sigma - u)) := norm_sum_le _ _
    _ <= ∑ u ∈ localZeros,
        (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Real) *
          (4 * (C + 1)) := by
      exact Finset.sum_le_sum fun u hu => hterm u hu
    _ = (∑ u ∈ localZeros,
        (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Real)) *
          (4 * (C + 1)) := by rw [Finset.sum_mul]
    _ <= C * (4 * (C + 1)) := by
      exact mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 4 * canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) *
        (canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) + 1) := by
      dsimp only [C]
      ring

theorem xiHorizontalLocalCoordinate_mem_innerClosedBall
    {sigma : Real}
    (hsigma : sigma ∈ Set.Icc guinandWeilXiContourLeft guinandWeilXiContourRight) :
    xiHorizontalLocalCoordinate sigma ∈
      closedBall (0 : Complex) (7 / 2 : Real) := by
  rw [mem_closedBall, dist_zero_right]
  have hsigmaUpper : sigma <= 5 / 4 := by
    simpa [guinandWeilXiContourRight] using hsigma.2
  have hsigmaLower : -(1 / 4 : Real) <= sigma := by
    have h := hsigma.1
    norm_num [guinandWeilXiContourLeft] at h ⊢
    linarith
  have hnonpos : sigma - 3 <= 0 := by linarith
  simp only [xiHorizontalLocalCoordinate, norm_real, Real.norm_eq_abs,
    abs_of_nonpos hnonpos]
  linarith

/-- Uniform form of the M80 local source bound.  The xi-growth constants are
fixed before the unit interval is selected, so this theorem can feed an
asymptotic sequence rather than a separate existential estimate at each
height. -/
theorem exists_fixed_canonicalXi_goodHeight_logDeriv_bound :
    ∃ K k A : Real,
      0 < K ∧ 0 < k ∧ 0 < A ∧
      ∀ N : Nat, 5 ≤ N → ∃ T : Real,
        (N : Real) <= T ∧ T <= N + 1 ∧
        ∀ sigma ∈ Set.Icc guinandWeilXiContourLeft guinandWeilXiContourRight,
          shiftedRiemannXi (xiLocalDiskCenter T)
                (xiHorizontalLocalCoordinate sigma) ≠ 0 ∧
            norm
                (logDeriv (shiftedRiemannXi (xiLocalDiskCenter T))
                  (xiHorizontalLocalCoordinate sigma)) <=
              128 * Real.log (xiLocalDiskGrowthFactor K k A T 4) +
                2 * canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) +
                4 * canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) *
                  (canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) + 1) := by
  obtain ⟨K, k, hK, hk, hboundary⟩ :=
    exists_shiftedRiemannXiBoundaryMajorant
  obtain ⟨A, hA, hxiInv⟩ :=
    exists_pos_const_norm_riemannXi_threeLine_inv_le_exp
  refine ⟨K, k, A, hK, hk, hA, ?_⟩
  intro N hN
  obtain ⟨T, hTN, hTN1, hsep⟩ :=
    exists_canonicalXi_goodHeight_below N (N + 5)
  refine ⟨T, hTN, hTN1, ?_⟩
  intro sigma hsigma
  let C := canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5)
  let localZeros :=
    shiftedRiemannXiOpenBallZeroFinset (xiLocalDiskCenter T) 4
  let principal : Complex :=
    ∑ u ∈ localZeros,
      (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Complex) /
        (xiHorizontalLocalCoordinate sigma - u)
  have hz := xiHorizontalLocalCoordinate_mem_innerClosedBall hsigma
  have hzmem := xiHorizontalLocalCoordinate_not_mem_localZeroFinset
    hN hTN hTN1 hsep sigma
  have hcount :
      (∑ u ∈ localZeros,
          (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Real)) <= C := by
    dsimp only [localZeros, C]
    exact sum_shiftedRiemannXiMultiplicity_localDisk_le_canonicalCount
      hN hTN hTN1
  have hprincipal : norm principal <= 4 * C * (C + 1) := by
    dsimp only [principal, localZeros, C]
    exact norm_xiLocalDisk_principalPart_le_canonicalCount
      hN hTN hTN1 hsep sigma
  have hresidual := norm_logDeriv_shiftedRiemannXi_sub_principalPart_le
    (c := xiLocalDiskCenter T) (R := 4) (r := 7 / 2)
    (M := shiftedRiemannXiBoundaryMajorant K k (xiLocalDiskCenter T) 4)
    (B := xiLocalDiskGrowthFactor K k A T 4)
    (z := xiHorizontalLocalCoordinate sigma)
    (by norm_num) (by norm_num)
    (one_lt_xiLocalDiskGrowthFactor hK hk hA (by norm_num))
    (riemannXi_xiLocalDiskCenter_ne_zero T)
    (hboundary (xiLocalDiskCenter T) 4 (by norm_num))
    (shiftedRiemannXiBoundaryMajorant_le_localGrowthFactor_mul_center
      hK (by norm_num) (hxiInv T)) hz hzmem
  have hresidual' :
      norm
          (logDeriv (shiftedRiemannXi (xiLocalDiskCenter T))
              (xiHorizontalLocalCoordinate sigma) - principal) <=
        128 * Real.log (xiLocalDiskGrowthFactor K k A T 4) + 2 * C := by
    dsimp only [principal, localZeros]
    norm_num at hresidual ⊢
    nlinarith
  have htriangle :
      norm
          (logDeriv (shiftedRiemannXi (xiLocalDiskCenter T))
            (xiHorizontalLocalCoordinate sigma)) <=
        norm
            (logDeriv (shiftedRiemannXi (xiLocalDiskCenter T))
              (xiHorizontalLocalCoordinate sigma) - principal) +
          norm principal := by
    have h := norm_add_le
      (logDeriv (shiftedRiemannXi (xiLocalDiskCenter T))
        (xiHorizontalLocalCoordinate sigma) - principal) principal
    simpa only [sub_add_cancel] using h
  have hzball : xiHorizontalLocalCoordinate sigma ∈ ball (0 : Complex) 4 := by
    rw [mem_ball, dist_zero_right]
    rw [mem_closedBall, dist_zero_right] at hz
    linarith
  have hnz : shiftedRiemannXi (xiLocalDiskCenter T)
      (xiHorizontalLocalCoordinate sigma) ≠ 0 := by
    intro hzero
    apply hzmem
    exact mem_shiftedRiemannXiOpenBallZeroFinset_iff.mpr ⟨hzball, hzero⟩
  exact ⟨hnz, by linarith⟩

/-- The interval-local compatibility form of the M80 logarithmic-derivative
bound. -/
theorem exists_canonicalXi_goodHeight_logDeriv_bound
    (N : Nat) (hN : 5 ≤ N) :
    ∃ T K k A : Real,
      (N : Real) <= T ∧ T <= N + 1 ∧
      0 < K ∧ 0 < k ∧ 0 < A ∧
      ∀ sigma ∈ Set.Icc guinandWeilXiContourLeft guinandWeilXiContourRight,
        norm
            (logDeriv (shiftedRiemannXi (xiLocalDiskCenter T))
              (xiHorizontalLocalCoordinate sigma)) <=
          128 * Real.log (xiLocalDiskGrowthFactor K k A T 4) +
            2 * canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) +
            4 * canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) *
              (canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) + 1) := by
  obtain ⟨K, k, A, hK, hk, hA, hbound⟩ :=
    exists_fixed_canonicalXi_goodHeight_logDeriv_bound
  obtain ⟨T, hTN, hTN1, hT⟩ := hbound N hN
  exact ⟨T, K, k, A, hTN, hTN1, hK, hk, hA,
    fun sigma hsigma => (hT sigma hsigma).2⟩

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
