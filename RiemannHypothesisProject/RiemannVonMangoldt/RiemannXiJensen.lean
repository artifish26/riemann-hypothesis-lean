import Mathlib.Analysis.Meromorphic.Divisor
import RiemannHypothesisProject.RiemannVonMangoldt.CanonicalMultiplicityGrowth
import RiemannHypothesisProject.RiemannVonMangoldt.RiemannXiMultiplicity

/-!
# Jensen bounds for the Riemann xi divisor

This file applies Mathlib's Jensen inequality on concentric closed balls
centered at `2`.  The inner radius is `r`, the outer radius is `2r`, so the
denominator is the fixed positive constant `log 2`.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open MeromorphicOn Metric Set

/-- Jensen's inequality applied to xi with the explicit finite-order sphere
majorant proved from the theta Mellin integral. -/
theorem exists_riemannXi_jensen_divisor_bound :
    ∃ K k : Real, 0 < K ∧ 0 < k ∧ ∀ r : Real, 0 < r →
      ∑ᶠ u, divisor riemannXi (closedBall (2 : Complex) r) u ≤
        Real.log (((2 * r + 2) * (2 * r + 3) * K *
          Real.exp (k * (2 * r + 4) ^ 2) + 1) /
            ‖riemannXi (2 : Complex)‖) / Real.log 2 := by
  obtain ⟨K, k, hK, hk, hsphere⟩ :=
    exists_riemannXi_sphere_quadraticExp_bound
  refine ⟨K, k, hK, hk, fun r hr ↦ ?_⟩
  let M : Real := (2 * r + 2) * (2 * r + 3) * K *
    Real.exp (k * (2 * r + 4) ^ 2) + 1
  have hM : 1 ≤ M := by
    dsimp [M]
    have hnonneg : 0 ≤ (2 * r + 2) * (2 * r + 3) * K *
        Real.exp (k * (2 * r + 4) ^ 2) := by positivity
    linarith
  have h2r : 0 < 2 * r := by positivity
  have hbound : ∀ z ∈ sphere (2 : Complex) |2 * r|, ‖riemannXi z‖ ≤ M := by
    intro z hz
    have hz' : z ∈ sphere (2 : Complex) (2 * r) := by
      simpa [abs_of_pos h2r] using hz
    simpa [M] using hsphere (2 * r) (by positivity) z hz'
  have hj := (analyticOnNhd_riemannXi (closedBall (2 : Complex) |2 * r|)).sum_divisor_le
    (c := (2 : Complex)) (r := r) (R := 2 * r) (M := M)
    (by simpa [abs_of_pos hr])
    (by rw [abs_of_pos hr, abs_of_pos h2r]; linarith)
    hM
    riemannXi_two_ne_zero
    hbound
  have hdiv : 2 * r / r = 2 := by field_simp
  rw [abs_of_pos hr] at hj
  simpa [M, hdiv] using hj

/-- Jensen's bound with the pure exponential sphere majorant. Taking the
logarithm exposes the quadratic polynomial directly. -/
theorem exists_riemannXi_jensen_quadratic_bound :
    ∃ A : Real, 0 < A ∧ ∀ r : Real, 0 < r →
      ∑ᶠ u, divisor riemannXi (closedBall (2 : Complex) r) u ≤
        (A * (2 * r + 4) ^ 2 - Real.log ‖riemannXi (2 : Complex)‖) /
          Real.log 2 := by
  obtain ⟨A, hA, hsphere⟩ := exists_riemannXi_sphere_exp_bound
  refine ⟨A, hA, fun r hr ↦ ?_⟩
  let M : Real := Real.exp (A * (2 * r + 4) ^ 2)
  have h2r : 0 < 2 * r := by positivity
  have hM : 1 ≤ M := by
    dsimp [M]
    exact Real.one_le_exp (by positivity)
  have hbound : ∀ z ∈ sphere (2 : Complex) |2 * r|, ‖riemannXi z‖ ≤ M := by
    intro z hz
    have hz' : z ∈ sphere (2 : Complex) (2 * r) := by
      simpa [abs_of_pos h2r] using hz
    simpa [M] using hsphere (2 * r) (by positivity) z hz'
  have hj := (analyticOnNhd_riemannXi (closedBall (2 : Complex) |2 * r|)).sum_divisor_le
    (c := (2 : Complex)) (r := r) (R := 2 * r) (M := M)
    (by simpa [abs_of_pos hr])
    (by rw [abs_of_pos hr, abs_of_pos h2r]; linarith)
    hM
    riemannXi_two_ne_zero
    hbound
  have hdiv : 2 * r / r = 2 := by field_simp
  have hnormpos : 0 < ‖riemannXi (2 : Complex)‖ :=
    norm_pos_iff.mpr riemannXi_two_ne_zero
  rw [abs_of_pos hr] at hj
  dsimp [M] at hj
  rw [Real.log_div (Real.exp_ne_zero _) hnormpos.ne', Real.log_exp] at hj
  simpa [hdiv] using hj

/-- Jensen's divisor bound with the real order `3 / 2` preserved. -/
theorem exists_riemannXi_jensen_rpowThreeHalves_bound :
    ∃ A : Real, 0 < A ∧ ∀ r : Real, 0 < r →
      ∑ᶠ u, divisor riemannXi (closedBall (2 : Complex) r) u ≤
        (A * (2 * r + 4) ^ (3 / 2 : Real) -
          Real.log ‖riemannXi (2 : Complex)‖) / Real.log 2 := by
  obtain ⟨A, hA, hsphere⟩ := exists_riemannXi_sphere_exp_rpowThreeHalves_bound
  refine ⟨A, hA, fun r hr ↦ ?_⟩
  let M : Real := Real.exp (A * (2 * r + 4) ^ (3 / 2 : Real))
  have h2r : 0 < 2 * r := by positivity
  have hM : 1 ≤ M := by
    dsimp [M]
    exact Real.one_le_exp (by positivity)
  have hbound : ∀ z ∈ sphere (2 : Complex) |2 * r|, ‖riemannXi z‖ ≤ M := by
    intro z hz
    have hz' : z ∈ sphere (2 : Complex) (2 * r) := by
      simpa [abs_of_pos h2r] using hz
    simpa [M] using hsphere (2 * r) (by positivity) z hz'
  have hj := (analyticOnNhd_riemannXi (closedBall (2 : Complex) |2 * r|)).sum_divisor_le
    (c := (2 : Complex)) (r := r) (R := 2 * r) (M := M)
    (by simpa [abs_of_pos hr])
    (by rw [abs_of_pos hr, abs_of_pos h2r]; linarith)
    hM
    riemannXi_two_ne_zero
    hbound
  have hdiv : 2 * r / r = 2 := by field_simp
  have hnormpos : 0 < ‖riemannXi (2 : Complex)‖ :=
    norm_pos_iff.mpr riemannXi_two_ne_zero
  rw [abs_of_pos hr] at hj
  dsimp [M] at hj
  rw [Real.log_div (Real.exp_ne_zero _) hnormpos.ne', Real.log_exp] at hj
  simpa [hdiv] using hj

/-- Jensen's divisor bound with the order-one `R*log R` sphere growth. -/
theorem exists_riemannXi_jensen_mulLog_bound :
    ∃ A : Real, 0 < A ∧ ∀ r : Real, 0 < r →
      ∑ᶠ u, divisor riemannXi (closedBall (2 : Complex) r) u ≤
        (A * (2 * r + 4) * (Real.log (2 * r + 4) + 1) -
          Real.log ‖riemannXi (2 : Complex)‖) / Real.log 2 := by
  obtain ⟨A, hA, hsphere⟩ := exists_riemannXi_sphere_exp_mulLog_bound
  refine ⟨A, hA, fun r hr ↦ ?_⟩
  let M : Real := Real.exp
    (A * (2 * r + 4) * (Real.log (2 * r + 4) + 1))
  have h2r : 0 < 2 * r := by positivity
  have hlog0 : 0 ≤ Real.log (2 * r + 4) :=
    Real.log_nonneg (by linarith)
  have hM : 1 ≤ M := by
    dsimp [M]
    exact Real.one_le_exp (by positivity)
  have hbound : ∀ z ∈ sphere (2 : Complex) |2 * r|, ‖riemannXi z‖ ≤ M := by
    intro z hz
    have hz' : z ∈ sphere (2 : Complex) (2 * r) := by
      simpa [abs_of_pos h2r] using hz
    simpa [M] using hsphere (2 * r) (by positivity) z hz'
  have hj := (analyticOnNhd_riemannXi (closedBall (2 : Complex) |2 * r|)).sum_divisor_le
    (c := (2 : Complex)) (r := r) (R := 2 * r) (M := M)
    (by simpa [abs_of_pos hr])
    (by rw [abs_of_pos hr, abs_of_pos h2r]; linarith)
    hM
    riemannXi_two_ne_zero
    hbound
  have hdiv : 2 * r / r = 2 := by field_simp
  have hnormpos : 0 < ‖riemannXi (2 : Complex)‖ :=
    norm_pos_iff.mpr riemannXi_two_ne_zero
  rw [abs_of_pos hr] at hj
  dsimp [M] at hj
  rw [Real.log_div (Real.exp_ne_zero _) hnormpos.ne', Real.log_exp] at hj
  simpa [hdiv] using hj

/-- The canonical positive-ordinate multiplicity window injects into the xi
divisor on a closed ball of radius `T + 3` around `2`. -/
theorem canonicalMultiplicityCount_le_riemannXi_divisor
    (T : Real) :
    canonicalPositiveOrdinateZetaZeroMultiplicityCount T ≤
      (((∑ᶠ u : Complex,
        divisor riemannXi (closedBall (2 : Complex) (T + 3)) u) : Int) : Real) := by
  let window : Finset ZetaZeroSubtype :=
    canonicalExactPositiveOrdinateZetaZeroWindow.window T
  let W : Finset Complex := window.image
    (fun rho : ZetaZeroSubtype ↦ (rho : Complex))
  let D : Complex → Real := fun u ↦
    (divisor riemannXi (closedBall (2 : Complex) (T + 3)) u : Real)
  have hanalytic : AnalyticOnNhd Complex riemannXi
      (closedBall (2 : Complex) (T + 3)) :=
    analyticOnNhd_riemannXi _
  have hmem (rho : ZetaZeroSubtype) (hrho : rho ∈ window) :
      (rho : Complex) ∈ closedBall (2 : Complex) (T + 3) := by
    have hwindow :=
      (canonicalExactPositiveOrdinateZetaZeroWindow.mem_window_iff T rho).mp hrho
    have hz : IsZetaZero (rho : Complex) :=
      mem_riemannZetaZeros.mp rho.property
    have hre_pos : 0 < (rho : Complex).re :=
      IsZetaZero.re_pos_of_im_pos hz hwindow.1
    have hre_lt : (rho : Complex).re < 1 := hz.re_lt_one
    have hnormrho : ‖(rho : Complex)‖ ≤ T + 1 := by
      calc
        ‖(rho : Complex)‖ ≤ |(rho : Complex).re| + |(rho : Complex).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = (rho : Complex).re + (rho : Complex).im := by
          rw [abs_of_pos hre_pos, abs_of_pos hwindow.1]
        _ ≤ T + 1 := by linarith
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖(rho : Complex) - 2‖ ≤ ‖(rho : Complex)‖ + ‖(2 : Complex)‖ :=
        norm_sub_le _ _
      _ ≤ T + 1 + 2 := by norm_num; linarith
      _ = T + 3 := by ring
  have hdivisor (rho : ZetaZeroSubtype) (hrho : rho ∈ window) :
      D (rho : Complex) = zetaZeroMultiplicityReal rho := by
    let rhoPos : PositiveOrdinateZetaZeroSubtype := ⟨rho,
      ((canonicalExactPositiveOrdinateZetaZeroWindow.mem_window_iff T rho).mp hrho).1⟩
    dsimp [D]
    rw [hanalytic.divisor_apply (hmem rho hrho)]
    rw [show analyticOrderAt riemannXi (rho : Complex) =
        zetaZeroMultiplicity rho by
      simpa [rhoPos] using analyticOrderAt_riemannXi_eq_zetaZeroMultiplicity rhoPos]
    simp [zetaZeroMultiplicityReal]
  have hcount_eq :
      canonicalPositiveOrdinateZetaZeroMultiplicityCount T = ∑ u ∈ W, D u := by
    unfold canonicalPositiveOrdinateZetaZeroMultiplicityCount
      multiplicityWeightedPositiveOrdinateHeightCountReal
    calc
      (∑ rho : {rho : ZetaZeroSubtype // rho ∈ window},
          zetaZeroMultiplicityReal rho.1) =
          ∑ rho ∈ window, zetaZeroMultiplicityReal rho := by
        symm
        rw [← Finset.sum_attach]
        simp only [Finset.attach_eq_univ]
      _ = ∑ u ∈ W, D u := by
        rw [show W = window.image
          (fun rho : ZetaZeroSubtype ↦ (rho : Complex)) by rfl]
        rw [Finset.sum_image]
        · exact Finset.sum_congr rfl fun rho hrho ↦ (hdivisor rho hrho).symm
        · intro a ha b hb hab
          exact Subtype.ext hab
  rw [hcount_eq]
  have hfinite :=
    (divisor riemannXi (closedBall (2 : Complex) (T + 3))).finiteSupport
      (isCompact_closedBall (2 : Complex) (T + 3))
  have hfiniteD : (Function.support D).Finite := hfinite.subset (by
    intro u hu
    have hne : (divisor riemannXi (closedBall (2 : Complex) (T + 3)) u) ≠ 0 := by
      intro hzero
      apply hu
      simp [D, hzero]
    simpa [Function.mem_support] using hne)
  let S : Finset Complex := hfiniteD.toFinset
  have hWS : W ⊆ S := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨rho, hrho, rfl⟩ := hu
    have hpositive : 0 < D (rho : Complex) := by
      rw [hdivisor rho hrho]
      exact zetaZeroMultiplicityReal_pos rho
    simpa [S, D, Function.mem_support] using hpositive.ne'
  calc
    (∑ u ∈ W, D u) ≤ ∑ u ∈ S, D u := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hWS fun u huS huW ↦ by
        dsimp [D]
        rw [hanalytic.divisor_apply]
        · simp
        · exact (show u ∈ closedBall (2 : Complex) (T + 3) by
            by_contra hu
            have hDne : D u ≠ 0 := by
              simpa [S, Function.mem_support] using huS
            apply hDne
            simp [D, divisor_def, hu])
    _ = ∑ᶠ u, D u := by
      symm
      exact finsum_eq_sum_of_support_subset D (by simp [S])
    _ = (((∑ᶠ u : Complex,
        divisor riemannXi (closedBall (2 : Complex) (T + 3)) u) : Int) : Real) := by
      symm
      simpa [D] using map_finsum (Int.castRingHom Real) hfinite

/-- The unconditional canonical analytic-multiplicity count with the
subquadratic exponent retained as a real power. -/
theorem exists_unconditional_canonicalMultiplicityCount_rpowThreeHalves_bound :
    ∃ C : Real, 0 < C ∧ ∀ T : Real, 0 ≤ T →
      canonicalPositiveOrdinateZetaZeroMultiplicityCount T ≤
        C * (T + 1) ^ (3 / 2 : Real) := by
  let A : Real := exists_riemannXi_jensen_rpowThreeHalves_bound.choose
  have hspec := exists_riemannXi_jensen_rpowThreeHalves_bound.choose_spec
  have hA : 0 < A := hspec.1
  have hjensen : ∀ r : Real, 0 < r →
      ∑ᶠ u, divisor riemannXi (closedBall (2 : Complex) r) u ≤
        (A * (2 * r + 4) ^ (3 / 2 : Real) -
          Real.log ‖riemannXi (2 : Complex)‖) / Real.log 2 := hspec.2
  let L : Real := |Real.log ‖riemannXi (2 : Complex)‖|
  let q : Real := (10 : Real) ^ (3 / 2 : Real)
  let C : Real := (A * q + L) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hC : 0 < C := by
    dsimp [C, L]
    positivity
  refine ⟨C, hC, fun T hT ↦ ?_⟩
  have hr : 0 < T + 3 := by linarith
  have hcount := canonicalMultiplicityCount_le_riemannXi_divisor T
  have hj := hjensen (T + 3) hr
  have hbase :
      canonicalPositiveOrdinateZetaZeroMultiplicityCount T ≤
        (A * (2 * (T + 3) + 4) ^ (3 / 2 : Real) -
          Real.log ‖riemannXi (2 : Complex)‖) / Real.log 2 :=
    hcount.trans hj
  have hlinear : 2 * (T + 3) + 4 ≤ 10 * (T + 1) := by linarith
  have hrpow : (2 * (T + 3) + 4) ^ (3 / 2 : Real) ≤
      (10 * (T + 1)) ^ (3 / 2 : Real) := by
    exact Real.rpow_le_rpow (by positivity) hlinear (by norm_num)
  have hfactor : (10 * (T + 1)) ^ (3 / 2 : Real) =
      q * (T + 1) ^ (3 / 2 : Real) := by
    dsimp [q]
    exact Real.mul_rpow (by positivity) (by positivity)
  have hrpowA : A * (2 * (T + 3) + 4) ^ (3 / 2 : Real) ≤
      A * q * (T + 1) ^ (3 / 2 : Real) := by
    calc
      A * (2 * (T + 3) + 4) ^ (3 / 2 : Real) ≤
          A * (10 * (T + 1)) ^ (3 / 2 : Real) :=
        mul_le_mul_of_nonneg_left hrpow hA.le
      _ = A * q * (T + 1) ^ (3 / 2 : Real) := by rw [hfactor]; ring
  have hone : 1 ≤ (T + 1) ^ (3 / 2 : Real) := by
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hL : L ≤ L * (T + 1) ^ (3 / 2 : Real) := by
    have hL0 : 0 ≤ L := abs_nonneg _
    nlinarith
  have hnum :
      A * (2 * (T + 3) + 4) ^ (3 / 2 : Real) -
          Real.log ‖riemannXi (2 : Complex)‖ ≤
        (A * q + L) * (T + 1) ^ (3 / 2 : Real) := by
    have hlog : -Real.log ‖riemannXi (2 : Complex)‖ ≤ L := by
      dsimp [L]
      exact neg_le_abs _
    nlinarith
  calc
    canonicalPositiveOrdinateZetaZeroMultiplicityCount T ≤
        (A * (2 * (T + 3) + 4) ^ (3 / 2 : Real) -
          Real.log ‖riemannXi (2 : Complex)‖) / Real.log 2 := hbase
    _ ≤ ((A * q + L) * (T + 1) ^ (3 / 2 : Real)) / Real.log 2 := by
      exact (div_le_div_iff_of_pos_right hlog2).mpr hnum
    _ = C * (T + 1) ^ (3 / 2 : Real) := by
      dsimp [C]
      ring

/-- The unconditional canonical analytic-multiplicity count in the classical
order-one `T*log T` shape. -/
theorem exists_unconditional_canonicalMultiplicityCount_mulLog_bound :
    ∃ C : Real, 0 < C ∧ ∀ T : Real, 0 ≤ T →
      canonicalPositiveOrdinateZetaZeroMultiplicityCount T ≤
        C * (T + 1) * (Real.log (T + 1) + 1) := by
  let A : Real := exists_riemannXi_jensen_mulLog_bound.choose
  have hspec := exists_riemannXi_jensen_mulLog_bound.choose_spec
  have hA : 0 < A := hspec.1
  have hjensen : ∀ r : Real, 0 < r →
      ∑ᶠ u, divisor riemannXi (closedBall (2 : Complex) r) u ≤
        (A * (2 * r + 4) * (Real.log (2 * r + 4) + 1) -
          Real.log ‖riemannXi (2 : Complex)‖) / Real.log 2 := hspec.2
  let L : Real := |Real.log ‖riemannXi (2 : Complex)‖|
  let d : Real := Real.log 10
  let q : Real := 10 * (d + 2)
  let C : Real := (A * q + L) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 ≤ d := by
    dsimp [d]
    exact Real.log_nonneg (by norm_num)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hC : 0 < C := by
    dsimp [C, L]
    positivity
  refine ⟨C, hC, fun T hT ↦ ?_⟩
  let u : Real := T + 1
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hr : 0 < T + 3 := by linarith
  have hcount := canonicalMultiplicityCount_le_riemannXi_divisor T
  have hj := hjensen (T + 3) hr
  have hbase :
      canonicalPositiveOrdinateZetaZeroMultiplicityCount T ≤
        (A * (2 * (T + 3) + 4) *
            (Real.log (2 * (T + 3) + 4) + 1) -
          Real.log ‖riemannXi (2 : Complex)‖) / Real.log 2 :=
    hcount.trans hj
  have hx : 0 < 2 * (T + 3) + 4 := by linarith
  have hlinear : 2 * (T + 3) + 4 ≤ 10 * u := by
    dsimp [u]
    linarith
  have hlog : Real.log (2 * (T + 3) + 4) ≤ Real.log (10 * u) :=
    Real.log_le_log hx hlinear
  have hlogProduct : Real.log (10 * u) = d + Real.log u := by
    dsimp [d]
    rw [Real.log_mul (by norm_num) (by positivity)]
  rw [hlogProduct] at hlog
  have hlogx0 : 0 ≤ Real.log (2 * (T + 3) + 4) :=
    Real.log_nonneg (by linarith)
  have hmul :
      (2 * (T + 3) + 4) * (Real.log (2 * (T + 3) + 4) + 1) ≤
        10 * u * (d + Real.log u + 1) := by
    exact mul_le_mul hlinear (by linarith) (by linarith) (by positivity)
  have hfactor : d + Real.log u + 1 ≤
      (d + 2) * (Real.log u + 1) := by
    nlinarith [mul_nonneg hd hlogu]
  have horder :
      (2 * (T + 3) + 4) * (Real.log (2 * (T + 3) + 4) + 1) ≤
        q * u * (Real.log u + 1) := by
    calc
      (2 * (T + 3) + 4) * (Real.log (2 * (T + 3) + 4) + 1) ≤
          10 * u * (d + Real.log u + 1) := hmul
      _ ≤ 10 * u * ((d + 2) * (Real.log u + 1)) := by
        exact mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = q * u * (Real.log u + 1) := by
        dsimp [q]
        ring
  have horderA :
      A * (2 * (T + 3) + 4) * (Real.log (2 * (T + 3) + 4) + 1) ≤
        A * q * u * (Real.log u + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left horder hA.le]
  have hone : 1 ≤ u * (Real.log u + 1) := by
    simpa only [one_mul] using
      (mul_le_mul hu (show 1 ≤ Real.log u + 1 by linarith)
        zero_le_one (zero_le_one.trans hu))
  have hL : L ≤ L * (u * (Real.log u + 1)) := by
    have hL0 : 0 ≤ L := abs_nonneg _
    nlinarith
  have hnum :
      A * (2 * (T + 3) + 4) * (Real.log (2 * (T + 3) + 4) + 1) -
          Real.log ‖riemannXi (2 : Complex)‖ ≤
        (A * q + L) * u * (Real.log u + 1) := by
    have hlogbase : -Real.log ‖riemannXi (2 : Complex)‖ ≤ L := by
      dsimp [L]
      exact neg_le_abs _
    nlinarith
  calc
    canonicalPositiveOrdinateZetaZeroMultiplicityCount T ≤
        (A * (2 * (T + 3) + 4) *
            (Real.log (2 * (T + 3) + 4) + 1) -
          Real.log ‖riemannXi (2 : Complex)‖) / Real.log 2 := hbase
    _ ≤ ((A * q + L) * u * (Real.log u + 1)) / Real.log 2 := by
      exact (div_le_div_iff_of_pos_right hlog2).mpr hnum
    _ = C * (T + 1) * (Real.log (T + 1) + 1) := by
      dsimp [C, u]
      ring

/-- Dyadic `T*log T` specialization of the unconditional order-one count. -/
theorem exists_unconditional_canonicalMultiplicityCount_dyadic_mulLog_bound :
    ∃ C : Real, 0 < C ∧ ∀ m : Nat,
      canonicalPositiveOrdinateZetaZeroMultiplicityCount
          ((2 : Real) ^ (m + 1)) ≤
        C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1))) := by
  obtain ⟨C, hC, hcount⟩ := exists_unconditional_canonicalMultiplicityCount_mulLog_bound
  refine ⟨4 * C, by positivity, fun m ↦ ?_⟩
  let T : Real := (2 : Real) ^ (m + 1)
  have hT : 1 ≤ T := by
    dsimp [T]
    exact one_le_pow₀ (by norm_num)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hTadd : T + 1 ≤ 2 * T := by linarith
  have hlog_m : Real.log (2 * T) = ((m : Real) + 2) * Real.log 2 := by
    dsimp [T]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlog : Real.log (T + 1) ≤ ((m : Real) + 2) * Real.log 2 := by
    calc
      Real.log (T + 1) ≤ Real.log (2 * T) :=
        Real.log_le_log (by positivity) hTadd
      _ = ((m : Real) + 2) * Real.log 2 := hlog_m
  have hlog2 : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)]
  have hlog_linear : Real.log (T + 1) + 1 ≤ 2 * ((m : Real) + 2) := by
    have hm0 : 0 ≤ (m : Real) + 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlog2 hm0
    nlinarith
  have hproduct :
      (T + 1) * (Real.log (T + 1) + 1) ≤
        4 * (((m : Real) + 2) * T) := by
    have hlog_nonneg : 0 ≤ Real.log (T + 1) + 1 := by
      have : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith)
      linarith
    have hm_nonneg : 0 ≤ 2 * ((m : Real) + 2) := by positivity
    calc
      (T + 1) * (Real.log (T + 1) + 1) ≤
          (2 * T) * (2 * ((m : Real) + 2)) :=
        mul_le_mul hTadd hlog_linear hlog_nonneg (by positivity)
      _ = 4 * (((m : Real) + 2) * T) := by ring
  have hsource := hcount T hTpos.le
  calc
    canonicalPositiveOrdinateZetaZeroMultiplicityCount
        ((2 : Real) ^ (m + 1)) ≤
      C * (T + 1) * (Real.log (T + 1) + 1) := by
        simpa [T] using hsource
    _ = C * ((T + 1) * (Real.log (T + 1) + 1)) := by ring
    _ ≤ C * (4 * (((m : Real) + 2) * T)) := by
      exact mul_le_mul_of_nonneg_left hproduct hC.le
    _ = (4 * C) * (((m : Real) + 2) * ((2 : Real) ^ (m + 1))) := by
      dsimp [T]
      ring

/-- The order-one xi/Jensen count consumed by the existing
multiplicity-aware inverse-square Li majorant theorem. -/
theorem unconditional_positiveOrdinateZetaZero_multiplicityHeightDecay_summable_of_mulLogCount :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 *
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  obtain ⟨C, hC, hcount⟩ :=
    exists_unconditional_canonicalMultiplicityCount_dyadic_mulLog_bound
  exact positiveOrdinateZetaZero_multiplicityHeightDecay_summable_of_exactCount
    canonicalExactPositiveOrdinateZetaZeroWindow C hC.le hcount

/-- The unconditional order-`3 / 2` count supplies multiplicity-weighted
inverse-square summability on the positive zero half. -/
theorem unconditional_positiveOrdinateZetaZero_multiplicityClampedInverseSquare_summable :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 /
        positiveOrdinateZetaZeroClampedHeight rho ^ 2) := by
  obtain ⟨C, hC, hcount⟩ :=
    exists_unconditional_canonicalMultiplicityCount_rpowThreeHalves_bound
  apply
    positiveOrdinateZetaZero_multiplicityClampedHeightDecay_summable_of_exactCount_rpow
      canonicalExactPositiveOrdinateZetaZeroWindow C (3 / 2 : Real) 2
      hC.le (by norm_num) (by norm_num)
  intro m
  exact hcount ((2 : Real) ^ (m + 1)) (by positivity)

/-- The same unconditional count, consumed by the actual critical-line
inverse-square height factor used in the multiplicity-aware Li majorant. -/
theorem unconditional_positiveOrdinateZetaZero_multiplicityHeightDecay_summable :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 *
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  have hclamped :=
    unconditional_positiveOrdinateZetaZero_multiplicityClampedInverseSquare_summable
  have hfive := Summable.mul_left (5 : Real) hclamped
  refine Summable.of_nonneg_of_le ?_ ?_ hfive
  · intro rho
    exact mul_nonneg (zetaZeroMultiplicityReal_pos rho.1).le (by positivity)
  · intro rho
    have hclamped_pos : 0 < positiveOrdinateZetaZeroClampedHeight rho := by
      unfold positiveOrdinateZetaZeroClampedHeight
      exact zero_lt_one.trans_le (le_max_left (1 : Real) _)
    have hden : positiveOrdinateZetaZeroClampedHeight rho ^ 2 <=
        positiveOrdinateZetaZeroClampedHeight rho ^ 2 + (1 / 2 : Real) ^ 2 := by
      norm_num
    have hinv :
        (positiveOrdinateZetaZeroClampedHeight rho ^ 2 +
            (1 / 2 : Real) ^ 2)⁻¹ <=
          (positiveOrdinateZetaZeroClampedHeight rho ^ 2)⁻¹ := by
      simpa [one_div] using
        one_div_le_one_div_of_le (pow_pos hclamped_pos 2) hden
    have hheight := positiveOrdinateZetaZero_heightDecay_le_five_mul_clamped rho
    have hfactor :
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ <=
          5 * (positiveOrdinateZetaZeroClampedHeight rho ^ 2)⁻¹ :=
      hheight.trans (mul_le_mul_of_nonneg_left hinv (by norm_num))
    have hmul := mul_le_mul_of_nonneg_left hfactor
      (zetaZeroMultiplicityReal_pos rho.1).le
    calc
      zetaZeroMultiplicityReal rho.1 *
          (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ <=
        zetaZeroMultiplicityReal rho.1 *
          (5 * (positiveOrdinateZetaZeroClampedHeight rho ^ 2)⁻¹) := hmul
      _ = 5 * (zetaZeroMultiplicityReal rho.1 /
          positiveOrdinateZetaZeroClampedHeight rho ^ 2) := by
        simp [div_eq_mul_inv]
        ring

/-- The unconditional polynomial growth certificate obtained from xi's
finite-order bound and Jensen's formula. -/
noncomputable def riemannXiCanonicalMultiplicityPolynomialGrowth :
    CanonicalMultiplicityPolynomialGrowth := by
  let A : Real := exists_riemannXi_jensen_quadratic_bound.choose
  have hspec := exists_riemannXi_jensen_quadratic_bound.choose_spec
  have hA : 0 < A := hspec.1
  have hjensen : ∀ r : Real, 0 < r →
      ∑ᶠ u, divisor riemannXi (closedBall (2 : Complex) r) u ≤
        (A * (2 * r + 4) ^ 2 - Real.log ‖riemannXi (2 : Complex)‖) /
          Real.log 2 := hspec.2
  let L : Real := |Real.log ‖riemannXi (2 : Complex)‖|
  let C : Real := (100 * A + L) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by
    dsimp [C, L]
    positivity
  refine
    { countConstant := C
      threshold := 0
      degree := 2
      countConstant_nonneg := hC
      count_le := ?_ }
  intro T hT
  have hr : 0 < T + 3 := by linarith
  have hcount := canonicalMultiplicityCount_le_riemannXi_divisor T
  have hj := hjensen (T + 3) hr
  have hbase :
      canonicalPositiveOrdinateZetaZeroMultiplicityCount T ≤
        (A * (2 * (T + 3) + 4) ^ 2 -
          Real.log ‖riemannXi (2 : Complex)‖) / Real.log 2 :=
    hcount.trans hj
  have hquad : (2 * (T + 3) + 4) ^ 2 ≤ 100 * (T + 1) ^ 2 := by
    nlinarith [sq_nonneg (T + 1), sq_nonneg (2 * (T + 3) + 4)]
  have hquadA : A * (2 * (T + 3) + 4) ^ 2 ≤
      100 * A * (T + 1) ^ 2 := by
    nlinarith
  have honeSq : 1 ≤ (T + 1) ^ 2 := by nlinarith [sq_nonneg T]
  have hL : L ≤ L * (T + 1) ^ 2 := by
    have hL0 : 0 ≤ L := abs_nonneg _
    nlinarith
  have hnum :
      A * (2 * (T + 3) + 4) ^ 2 -
          Real.log ‖riemannXi (2 : Complex)‖ ≤
        (100 * A + L) * (T + 1) ^ 2 := by
    have hlog : -Real.log ‖riemannXi (2 : Complex)‖ ≤ L := by
      dsimp [L]
      exact neg_le_abs _
    nlinarith
  calc
    canonicalPositiveOrdinateZetaZeroMultiplicityCount T ≤
        (A * (2 * (T + 3) + 4) ^ 2 -
          Real.log ‖riemannXi (2 : Complex)‖) / Real.log 2 := hbase
    _ ≤ ((100 * A + L) * (T + 1) ^ 2) / Real.log 2 := by
      exact (div_le_div_iff_of_pos_right hlog2).mpr hnum
    _ = C * (T + 1) ^ (2 : Nat) := by
      dsimp [C]
      ring

/-- Existence form used by source-theorem consumers. -/
theorem exists_unconditional_CanonicalMultiplicityPolynomialGrowth :
    Nonempty CanonicalMultiplicityPolynomialGrowth :=
  ⟨riemannXiCanonicalMultiplicityPolynomialGrowth⟩


end

end ComplexCompactExhaustion

end RiemannHypothesisProject
