import RiemannHypothesisProject.GuinandWeilConcrete.XiLocalGoodHeightBound
import RiemannHypothesisProject.GuinandWeilConcrete.XiRectangleIdentity

/-!
# Gaussian decay of the xi horizontal contour edges

This module consumes the M80 good-height logarithmic-derivative theorem and
the polynomial-Gaussian contour-weight estimate.  The first source theorem
exports an explicit norm bound for the complete upper horizontal integral at
a selected height in every sufficiently high unit interval.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open Complex Filter Metric Set
open scoped Interval Topology

/-- A convenient logarithmic estimate for the positive exponential factors
appearing in the local xi growth majorant. -/
theorem log_exp_add_one_le_add_one {y : Real} (hy : 0 <= y) :
    Real.log (Real.exp y + 1) <= y + 1 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  calc
    Real.exp y + 1 <= Real.exp y + Real.exp y := by
      gcongr
      exact Real.one_le_exp hy
    _ = Real.exp y * 2 := by ring
    _ <= Real.exp y * Real.exp 1 := by
      gcongr
      nlinarith [Real.add_one_le_exp 1]
    _ = Real.exp (y + 1) := by rw [Real.exp_add]

/-- The logarithm of the denominator-free local xi growth factor has a fixed
quadratic majorant.  This deliberately coarse estimate is sufficient for the
Gaussian horizontal-edge limit. -/
theorem exists_pos_const_log_xiLocalDiskGrowthFactor_le_sq
    {K k A : Real} (hK : 0 < K) (hk : 0 < k) (hA : 0 < A) :
    exists D : Real, 0 < D /\ forall T : Real,
      Real.log (xiLocalDiskGrowthFactor K k A T 4) <=
        D * (abs T + 10) ^ 2 := by
  let D : Real := K + k + A + Real.pi + 16
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro T
  let c : Real := norm (xiLocalDiskCenter T)
  let u : Real := c + 4
  let v : Real := c + 5
  let z : Real := k * (c + 6) ^ (3 / 2 : Real)
  let P : Real := u * v * K
  let M : Real := shiftedRiemannXiBoundaryMajorant K k (xiLocalDiskCenter T) 4
  let y : Real := Real.pi * (abs T + 1)
  let E : Real := A * Real.exp y
  have hc : 0 <= c := by dsimp [c]; positivity
  have hu : 0 <= u := by dsimp [u]; positivity
  have hv : 0 <= v := by dsimp [v]; positivity
  have hz : 0 <= z := by dsimp [z]; positivity
  have hP : 0 <= P := by dsimp [P]; positivity
  have hy : 0 <= y := by dsimp [y]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hM : 0 < M := by
    dsimp [M, shiftedRiemannXiBoundaryMajorant, P, u, v, z]
    positivity
  have hgrowth :
      xiLocalDiskGrowthFactor K k A T 4 = M * E + 1 := by
    rfl
  have hfactor : M * E + 1 <= (M + 1) * (E + 1) := by
    nlinarith [hM.le, hE.le]
  have hlogSplit :
      Real.log (xiLocalDiskGrowthFactor K k A T 4) <=
        Real.log (M + 1) + Real.log (E + 1) := by
    rw [hgrowth]
    calc
      Real.log (M * E + 1) <= Real.log ((M + 1) * (E + 1)) :=
        Real.log_le_log (by positivity) hfactor
      _ = Real.log (M + 1) + Real.log (E + 1) := by
        rw [Real.log_mul (by positivity) (by positivity)]
  have hMformula : M = (P * Real.exp z + 1) / 2 := by
    dsimp [M, P, z, u, v, c, shiftedRiemannXiBoundaryMajorant]
    ring
  have hMcoarse : M + 1 <= P * Real.exp z + 3 := by
    rw [hMformula]
    nlinarith [mul_nonneg hP (Real.exp_pos z).le]
  have hPfactor :
      P * Real.exp z + 3 <= (P + 3) * (Real.exp z + 1) := by
    nlinarith [hP, (Real.exp_pos z).le]
  have hPcoarse : P + 3 <= (u + 1) * (v + 1) * (K + 3) := by
    have hdiff :
        0 <= u * v * 3 + u * (K + 3) + v * (K + 3) + (K + 3) := by
      positivity
    dsimp [P]
    nlinarith
  have hlogP : Real.log (P + 3) <= u + v + K + 2 := by
    have hpositive : 0 < P + 3 := by positivity
    calc
      Real.log (P + 3) <= Real.log ((u + 1) * (v + 1) * (K + 3)) :=
        Real.log_le_log hpositive hPcoarse
      _ = Real.log (u + 1) + Real.log (v + 1) + Real.log (K + 3) := by
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity)]
      _ <= u + v + K + 2 := by
        have huLog := Real.log_le_sub_one_of_pos (show 0 < u + 1 by positivity)
        have hvLog := Real.log_le_sub_one_of_pos (show 0 < v + 1 by positivity)
        have hKLog := Real.log_le_sub_one_of_pos (show 0 < K + 3 by positivity)
        linarith
  have hlogM : Real.log (M + 1) <= u + v + K + z + 3 := by
    calc
      Real.log (M + 1) <= Real.log (P * Real.exp z + 3) :=
        Real.log_le_log (by positivity) hMcoarse
      _ <= Real.log ((P + 3) * (Real.exp z + 1)) :=
        Real.log_le_log (by positivity) hPfactor
      _ = Real.log (P + 3) + Real.log (Real.exp z + 1) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ <= u + v + K + z + 3 := by
        linarith [hlogP, log_exp_add_one_le_add_one hz]
  have hEfactor : E + 1 <= (A + 1) * (Real.exp y + 1) := by
    dsimp [E]
    nlinarith [hA.le, (Real.exp_pos y).le]
  have hlogE : Real.log (E + 1) <= A + y + 1 := by
    calc
      Real.log (E + 1) <= Real.log ((A + 1) * (Real.exp y + 1)) :=
        Real.log_le_log (by positivity) hEfactor
      _ = Real.log (A + 1) + Real.log (Real.exp y + 1) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ <= A + y + 1 := by
        have hALog := Real.log_le_sub_one_of_pos (show 0 < A + 1 by positivity)
        linarith [log_exp_add_one_le_add_one hy]
  have hcBound : c <= abs T + 3 := by
    dsimp [c, xiLocalDiskCenter]
    calc
      norm ((3 : Complex) + Complex.I * (T : Complex)) <=
          norm (3 : Complex) + norm (Complex.I * (T : Complex)) := norm_add_le _ _
      _ = abs T + 3 := by simp [add_comm]
  have hbase : 1 <= abs T + 10 := by nlinarith [abs_nonneg T]
  have hrpow : (c + 6) ^ (3 / 2 : Real) <= (abs T + 10) ^ 2 := by
    have hc6 : c + 6 <= abs T + 10 := by linarith
    calc
      (c + 6) ^ (3 / 2 : Real) <= (abs T + 10) ^ (3 / 2 : Real) := by
        exact Real.rpow_le_rpow (by positivity) hc6 (by norm_num)
      _ <= (abs T + 10) ^ (2 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
      _ = (abs T + 10) ^ 2 := by norm_num
  have hlinear : abs T + 1 <= (abs T + 10) ^ 2 := by nlinarith [abs_nonneg T]
  have hconstant : 1 <= (abs T + 10) ^ 2 := by nlinarith
  have hbaseSq : abs T + 10 <= (abs T + 10) ^ 2 := by nlinarith
  have hcSq : c <= (abs T + 10) ^ 2 := by linarith
  have hcoarse :
      u + v + K + z + 3 + (A + y + 1) <=
        D * (abs T + 10) ^ 2 := by
    dsimp [u, v, z, y, D]
    have hkGrowth := mul_le_mul_of_nonneg_left hrpow hk.le
    have hpiGrowth := mul_le_mul_of_nonneg_left hlinear Real.pi_pos.le
    have hKConstant := mul_le_mul_of_nonneg_left hconstant hK.le
    have hAConstant := mul_le_mul_of_nonneg_left hconstant hA.le
    nlinarith
  exact hlogSplit.trans ((add_le_add hlogM hlogE).trans hcoarse)

/-- Translation does not change the logarithmic derivative, apart from
evaluating it at the translated point. -/
theorem logDeriv_shiftedRiemannXi (c z : Complex) :
    logDeriv (shiftedRiemannXi c) z = logDeriv riemannXi (c + z) := by
  rw [logDeriv_apply, logDeriv_apply]
  change deriv (fun w : Complex => riemannXi (c + w)) z /
      riemannXi (c + z) = _
  rw [deriv_comp_const_add]

/-- Xi's logarithmic derivative is odd under `s |-> 1 - s`.  This identity
holds at every point because the reflection laws identify both numerator and
denominator; no nonvanishing assumption is needed. -/
theorem logDeriv_riemannXi_one_sub_all (s : Complex) :
    logDeriv riemannXi (1 - s) = -logDeriv riemannXi s := by
  have hfunctions :
      (fun z : Complex => riemannXi (1 - z)) = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  have hderiv :
      deriv (fun z : Complex => riemannXi (1 - z)) s =
        deriv riemannXi s := by
    rw [hfunctions]
  have hchain :
      deriv (fun z : Complex => riemannXi (1 - z)) s =
        -deriv riemannXi (1 - s) := by
    rw [show (fun z : Complex => riemannXi (1 - z)) =
      riemannXi ∘ (fun z : Complex => 1 - z) by rfl]
    rw [deriv_comp s differentiable_riemannXi.differentiableAt (by fun_prop)]
    simp
  rw [logDeriv_apply, logDeriv_apply, riemannXi_one_sub]
  rw [hchain] at hderiv
  rw [← neg_div]
  congr 1
  linear_combination -hderiv

/-- The complete weighted xi logarithmic-derivative integrand is odd under
reflection, without a separate nonvanishing hypothesis. -/
theorem guinandWeilXiContourWeight_mul_logDeriv_one_sub_all
    (p : Polynomial Real) (s : Complex) :
    guinandWeilXiContourWeight p (1 - s) *
        logDeriv riemannXi (1 - s) =
      -(guinandWeilXiContourWeight p s * logDeriv riemannXi s) := by
  rw [guinandWeilXiContourWeight_one_sub,
    logDeriv_riemannXi_one_sub_all]
  ring

/-- The explicit right-hand side of the M80 logarithmic-derivative bound. -/
def xiGoodHeightLogDerivEnvelope
    (K k A : Real) (N : Nat) (T : Real) : Real :=
  128 * Real.log (xiLocalDiskGrowthFactor K k A T 4) +
    2 * canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) +
    4 * canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) *
      (canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5) + 1)

/-- On a selected unit interval, the complete M80 envelope has polynomial
growth of degree at most four. -/
theorem exists_pos_const_xiGoodHeightLogDerivEnvelope_le_pow_four
    {K k A : Real} (hK : 0 < K) (hk : 0 < k) (hA : 0 < A) :
    exists B : Real, 0 < B /\
      forall (N : Nat) (T : Real), 5 <= N ->
        (N : Real) <= T -> T <= N + 1 ->
        xiGoodHeightLogDerivEnvelope K k A N T <=
          B * ((N : Real) + 11) ^ 4 := by
  obtain ⟨D, hD, hlog⟩ :=
    exists_pos_const_log_xiLocalDiskGrowthFactor_le_sq hK hk hA
  obtain ⟨C, hC, hcount⟩ :=
    exists_unconditional_canonicalMultiplicityCount_rpowThreeHalves_bound
  let B : Real := 128 * D + 2 * C + 4 * C * (C + 1)
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro N T hN hTN hTN1
  let X : Real := (N : Real) + 11
  let Z : Real := canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 5)
  have hN0 : 0 <= (N : Real) := by positivity
  have hT0 : 0 <= T := hN0.trans hTN
  have hX1 : 1 <= X := by dsimp [X]; linarith
  have hX0 : 0 <= X := zero_le_one.trans hX1
  have hT_X : abs T + 10 <= X := by
    rw [abs_of_nonneg hT0]
    dsimp [X]
    norm_num at hTN1 ⊢
    linarith
  have hlogT := hlog T
  have hlogBound :
      Real.log (xiLocalDiskGrowthFactor K k A T 4) <= D * X ^ 2 := by
    exact hlogT.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hT_X 2) hD.le)
  have hcountRaw := hcount ((N : Real) + 5) (by positivity)
  have hcountU : Z <= C * ((N : Real) + 6) ^ (3 / 2 : Real) := by
    have hbaseEq : (N : Real) + 5 + 1 = (N : Real) + 6 := by ring
    rw [hbaseEq] at hcountRaw
    exact hcountRaw
  have hU1 : 1 <= (N : Real) + 6 := by linarith
  have hrpowU :
      ((N : Real) + 6) ^ (3 / 2 : Real) <= ((N : Real) + 6) ^ 2 := by
    calc
      ((N : Real) + 6) ^ (3 / 2 : Real) <=
          ((N : Real) + 6) ^ (2 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
      _ = ((N : Real) + 6) ^ 2 := by norm_num
  have hUX : ((N : Real) + 6) ^ 2 <= X ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) (by dsimp [X]; linarith) 2
  have hZX : Z <= C * X ^ 2 := by
    exact hcountU.trans (mul_le_mul_of_nonneg_left
      (hrpowU.trans hUX) hC.le)
  have hZ0 : 0 <= Z := by
    exact canonicalPositiveOrdinateZetaZeroMultiplicityCount_nonneg _
  have hXsq1 : 1 <= X ^ 2 := by nlinarith
  have hZadd : Z + 1 <= (C + 1) * X ^ 2 := by
    have hCconstant := mul_le_mul_of_nonneg_left hXsq1 hC.le
    nlinarith
  have hZproduct : Z * (Z + 1) <= C * (C + 1) * X ^ 4 := by
    calc
      Z * (Z + 1) <= (C * X ^ 2) * ((C + 1) * X ^ 2) :=
        mul_le_mul hZX hZadd (by linarith) (by positivity)
      _ = C * (C + 1) * X ^ 4 := by ring
  have hXpow : X ^ 2 <= X ^ 4 := by nlinarith [hXsq1]
  have hlogFour : D * X ^ 2 <= D * X ^ 4 :=
    mul_le_mul_of_nonneg_left hXpow hD.le
  have hZFour : Z <= C * X ^ 4 :=
    hZX.trans (mul_le_mul_of_nonneg_left hXpow hC.le)
  dsimp only [xiGoodHeightLogDerivEnvelope]
  change 128 * Real.log (xiLocalDiskGrowthFactor K k A T 4) +
      2 * Z + 4 * Z * (Z + 1) <= B * X ^ 4
  dsimp [B]
  nlinarith

/-- A fixed polynomial in a shifted natural height is dominated by a genuine
Gaussian. -/
theorem tendsto_natCast_add_pow_mul_exp_neg_mul_sq
    (n : Nat) {a b : Real} (ha : 0 <= a) (hb : 0 < b) :
    Tendsto
      (fun N : Nat => ((N : Real) + a) ^ n *
        Real.exp (-b * (N : Real) ^ 2))
      atTop (nhds 0) := by
  have hnat : Tendsto (fun N : Nat => (N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hpowReal :=
    tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (n : Real)
  have hpow : Tendsto
      (fun N : Nat => (N : Real) ^ n * Real.exp (-b * (N : Real) ^ 2))
      atTop (nhds 0) := by
    have h := hpowReal.mono_left atTop_le_cocompact
    have hcomp := h.comp hnat
    convert hcomp using 1
    funext N
    simp only [Function.comp_apply,
      abs_of_nonneg (show (0 : Real) <= (N : Real) by positivity),
      Real.rpow_natCast]
  have hzeroReal :=
    tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (0 : Real)
  have hzero : Tendsto
      (fun N : Nat => Real.exp (-b * (N : Real) ^ 2))
      atTop (nhds 0) := by
    have h := hzeroReal.mono_left atTop_le_cocompact
    have hcomp := h.comp hnat
    convert hcomp using 1
    funext N
    simp only [Function.comp_apply, Real.rpow_zero, one_mul]
  have hmajor : Tendsto
      (fun N : Nat =>
        2 ^ (n - 1) *
          ((N : Real) ^ n * Real.exp (-b * (N : Real) ^ 2) +
            a ^ n * Real.exp (-b * (N : Real) ^ 2)))
      atTop (nhds 0) := by
    convert (hpow.add (hzero.const_mul (a ^ n))).const_mul (2 ^ (n - 1)) using 1 <;>
      ring
  exact squeeze_zero
    (fun N => mul_nonneg (pow_nonneg (by positivity) n) (Real.exp_pos _).le)
    (fun N => by
      have hadd := add_pow_le (show 0 <= (N : Real) by positivity) ha n
      exact (mul_le_mul_of_nonneg_right hadd (Real.exp_pos _).le).trans_eq (by ring))
    hmajor

/-- M80 in the global xi coordinates used by the rectangle integral. -/
theorem exists_canonicalXi_goodHeight_global_logDeriv_bound
    (N : Nat) (hN : 5 <= N) :
    exists T K k A : Real,
      (N : Real) <= T /\ T <= N + 1 /\
      0 < K /\ 0 < k /\ 0 < A /\
      forall sigma, sigma ∈
          Set.Icc guinandWeilXiContourLeft guinandWeilXiContourRight ->
        norm (logDeriv riemannXi
          ((sigma : Complex) + (T : Complex) * Complex.I)) <=
          xiGoodHeightLogDerivEnvelope K k A N T := by
  obtain ⟨T, K, k, A, hTN, hTN1, hK, hk, hA, hbound⟩ :=
    exists_canonicalXi_goodHeight_logDeriv_bound N hN
  refine ⟨T, K, k, A, hTN, hTN1, hK, hk, hA, ?_⟩
  intro sigma hsigma
  have h := hbound sigma hsigma
  rw [logDeriv_shiftedRiemannXi] at h
  have hcoordinate :
      xiLocalDiskCenter T + xiHorizontalLocalCoordinate sigma =
        (sigma : Complex) + (T : Complex) * Complex.I := by
    simp only [xiLocalDiskCenter, xiHorizontalLocalCoordinate]
    push_cast
    ring
  rw [hcoordinate] at h
  simpa only [xiGoodHeightLogDerivEnvelope] using h

/-- Uniform global-coordinate form of M80.  Its growth constants are fixed
across all sufficiently high unit intervals. -/
theorem exists_fixed_canonicalXi_goodHeight_global_logDeriv_bound :
    exists K k A : Real,
      0 < K /\ 0 < k /\ 0 < A /\
      forall N : Nat, 5 <= N -> exists T : Real,
        (N : Real) <= T /\ T <= N + 1 /\
        forall sigma, sigma ∈
            Set.Icc guinandWeilXiContourLeft guinandWeilXiContourRight ->
          riemannXi ((sigma : Complex) + (T : Complex) * Complex.I) ≠ 0 /\
            norm (logDeriv riemannXi
              ((sigma : Complex) + (T : Complex) * Complex.I)) <=
              xiGoodHeightLogDerivEnvelope K k A N T := by
  obtain ⟨K, k, A, hK, hk, hA, hbound⟩ :=
    exists_fixed_canonicalXi_goodHeight_logDeriv_bound
  refine ⟨K, k, A, hK, hk, hA, ?_⟩
  intro N hN
  obtain ⟨T, hTN, hTN1, hlocal⟩ := hbound N hN
  refine ⟨T, hTN, hTN1, ?_⟩
  intro sigma hsigma
  have h := (hlocal sigma hsigma).2
  have hnz := (hlocal sigma hsigma).1
  rw [logDeriv_shiftedRiemannXi] at h
  have hcoordinate :
      xiLocalDiskCenter T + xiHorizontalLocalCoordinate sigma =
        (sigma : Complex) + (T : Complex) * Complex.I := by
    simp only [xiLocalDiskCenter, xiHorizontalLocalCoordinate]
    push_cast
    ring
  change riemannXi
      (xiLocalDiskCenter T + xiHorizontalLocalCoordinate sigma) ≠ 0 at hnz
  rw [hcoordinate] at hnz
  rw [hcoordinate] at h
  exact ⟨hnz, by simpa only [xiGoodHeightLogDerivEnvelope] using h⟩

/-- A uniform logarithmic-derivative estimate on one horizontal edge turns
the pointwise polynomial-Gaussian weight bound into a bound for the complete
edge integral. -/
theorem norm_guinandWeilXi_horizontalIntegral_le
    (p : Polynomial Real) (N : Nat) (T K k A C : Real)
    (hC : 0 <= C)
    (hweight : forall sigma : Real,
      guinandWeilXiContourLeft <= sigma ->
      sigma <= guinandWeilXiContourRight ->
      norm (guinandWeilXiContourWeight p
        ((sigma : Complex) + (T : Complex) * Complex.I)) <=
        C * (abs T + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
          Real.exp (-Real.pi * T ^ 2))
    (hlogDeriv : forall sigma,
      sigma ∈ Set.Icc guinandWeilXiContourLeft guinandWeilXiContourRight ->
      norm (logDeriv riemannXi
        ((sigma : Complex) + (T : Complex) * Complex.I)) <=
        xiGoodHeightLogDerivEnvelope K k A N T) :
    norm
        (guinandWeilHorizontalIntegral
          (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
          guinandWeilXiContourLeft guinandWeilXiContourRight T) <=
      C * (abs T + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
          Real.exp (-Real.pi * T ^ 2) *
        xiGoodHeightLogDerivEnvelope K k A N T * (3 / 2 : Real) := by
  let W : Real :=
    C * (abs T + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
      Real.exp (-Real.pi * T ^ 2)
  let E : Real := xiGoodHeightLogDerivEnvelope K k A N T
  have hE : 0 <= E := by
    have hleft : guinandWeilXiContourLeft ∈
        Set.Icc guinandWeilXiContourLeft guinandWeilXiContourRight := by
      constructor
      · exact le_rfl
      · norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight]
    exact (norm_nonneg _).trans (hlogDeriv _ hleft)
  have hW : 0 <= W := by
    dsimp only [W]
    positivity
  unfold guinandWeilHorizontalIntegral
  calc
    norm
        (∫ sigma in guinandWeilXiContourLeft..guinandWeilXiContourRight,
          guinandWeilXiContourWeight p
              ((sigma : Complex) + (T : Complex) * Complex.I) *
            logDeriv riemannXi
              ((sigma : Complex) + (T : Complex) * Complex.I)) <=
        (W * E) *
          abs (guinandWeilXiContourRight - guinandWeilXiContourLeft) := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro sigma hsigma
      have hsigma' := Set.uIoc_subset_uIcc hsigma
      rw [Set.uIcc_of_le (by
        norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight])] at hsigma'
      rw [norm_mul]
      calc
        norm
              (guinandWeilXiContourWeight p
                ((sigma : Complex) + (T : Complex) * Complex.I)) *
            norm
              (logDeriv riemannXi
                ((sigma : Complex) + (T : Complex) * Complex.I)) <=
            W *
              norm
                (logDeriv riemannXi
                  ((sigma : Complex) + (T : Complex) * Complex.I)) := by
          exact mul_le_mul_of_nonneg_right
            (by
              dsimp only [W]
              exact hweight sigma hsigma'.1 hsigma'.2)
            (norm_nonneg _)
        _ <= W * E := mul_le_mul_of_nonneg_left
          (hlogDeriv sigma hsigma') hW
    _ = C * (abs T + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
          Real.exp (-Real.pi * T ^ 2) *
        xiGoodHeightLogDerivEnvelope K k A N T * (3 / 2 : Real) := by
      dsimp only [W, E]
      norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight]

/-- In every sufficiently high unit interval, the complete upper horizontal
xi integral is bounded by the product of the explicit M80 envelope and the
polynomial-Gaussian edge factor. -/
theorem exists_canonicalXi_goodHeight_horizontalIntegral_bound
    (p : Polynomial Real) (N : Nat) (hN : 5 <= N) :
    exists T K k A C : Real,
      (N : Real) <= T /\ T <= N + 1 /\
      0 < K /\ 0 < k /\ 0 < A /\ 0 < C /\
      norm
          (guinandWeilHorizontalIntegral
            (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
            guinandWeilXiContourLeft guinandWeilXiContourRight T) <=
        C * (abs T + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
            Real.exp (-Real.pi * T ^ 2) *
          xiGoodHeightLogDerivEnvelope K k A N T * (3 / 2 : Real) := by
  obtain ⟨T, K, k, A, hTN, hTN1, hK, hk, hA, hlogDeriv⟩ :=
    exists_canonicalXi_goodHeight_global_logDeriv_bound N hN
  obtain ⟨C, hC, hweight⟩ :=
    exists_pos_const_norm_guinandWeilXiContourWeight_horizontal_le p
  refine ⟨T, K, k, A, C, hTN, hTN1, hK, hk, hA, hC, ?_⟩
  exact norm_guinandWeilXi_horizontalIntegral_le p N T K k A C hC.le
    (fun sigma hsigmaLower hsigmaUpper =>
      hweight sigma T hsigmaLower hsigmaUpper) hlogDeriv

/-- Reflection across the critical line identifies the lower horizontal
integral with the negative upper horizontal integral. -/
theorem guinandWeilXi_horizontalIntegral_neg
    (p : Polynomial Real) (T : Real) :
    guinandWeilHorizontalIntegral
        (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
        guinandWeilXiContourLeft guinandWeilXiContourRight (-T) =
      -guinandWeilHorizontalIntegral
        (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
        guinandWeilXiContourLeft guinandWeilXiContourRight T := by
  let F : Complex -> Complex := fun s =>
    guinandWeilXiContourWeight p s * logDeriv riemannXi s
  have hpoint : forall sigma : Real,
      F ((sigma : Complex) + (-T : Complex) * Complex.I) =
        -F (((1 - sigma : Real) : Complex) + (T : Complex) * Complex.I) := by
    intro sigma
    have hreflect :=
      guinandWeilXiContourWeight_mul_logDeriv_one_sub_all p
        (((1 - sigma : Real) : Complex) + (T : Complex) * Complex.I)
    change F (1 - (((1 - sigma : Real) : Complex) +
        (T : Complex) * Complex.I)) =
      -F (((1 - sigma : Real) : Complex) +
        (T : Complex) * Complex.I) at hreflect
    convert hreflect using 1 <;> push_cast <;> ring_nf
  unfold guinandWeilHorizontalIntegral
  change (∫ sigma in guinandWeilXiContourLeft..guinandWeilXiContourRight,
      F ((sigma : Complex) + ((-T : Real) : Complex) * Complex.I)) = _
  rw [intervalIntegral.integral_congr (fun sigma _hsigma => by
        simpa using hpoint sigma),
    intervalIntegral.integral_neg]
  have hsub := intervalIntegral.integral_comp_sub_left
    (f := fun sigma : Real =>
      F ((sigma : Complex) + (T : Complex) * Complex.I))
    (a := guinandWeilXiContourLeft)
    (b := guinandWeilXiContourRight) 1
  have hsub' :
      (∫ sigma in guinandWeilXiContourLeft..guinandWeilXiContourRight,
        F (1 - (sigma : Complex) + (T : Complex) * Complex.I)) =
      ∫ sigma in (1 - guinandWeilXiContourRight)..(1 - guinandWeilXiContourLeft),
        F ((sigma : Complex) + (T : Complex) * Complex.I) := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one] using hsub
  rw [hsub']
  norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight]
  rfl

/-- The selected good height controls both horizontal edges by the same
explicit scalar envelope. -/
theorem exists_canonicalXi_goodHeight_both_horizontalIntegral_bound
    (p : Polynomial Real) (N : Nat) (hN : 5 <= N) :
    exists T K k A C : Real,
      (N : Real) <= T /\ T <= N + 1 /\
      0 < K /\ 0 < k /\ 0 < A /\ 0 < C /\
      let bound :=
        C * (abs T + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
            Real.exp (-Real.pi * T ^ 2) *
          xiGoodHeightLogDerivEnvelope K k A N T * (3 / 2 : Real)
      norm
          (guinandWeilHorizontalIntegral
            (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
            guinandWeilXiContourLeft guinandWeilXiContourRight T) <= bound /\
        norm
          (guinandWeilHorizontalIntegral
            (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
            guinandWeilXiContourLeft guinandWeilXiContourRight (-T)) <= bound := by
  obtain ⟨T, K, k, A, C, hTN, hTN1, hK, hk, hA, hC, hupper⟩ :=
    exists_canonicalXi_goodHeight_horizontalIntegral_bound p N hN
  refine ⟨T, K, k, A, C, hTN, hTN1, hK, hk, hA, hC, hupper, ?_⟩
  rw [guinandWeilXi_horizontalIntegral_neg, norm_neg]
  exact hupper

/-- Fixed-constant receiving surface: every sufficiently high unit
interval contains a height at which both horizontal xi contour edges satisfy
the same explicit Gaussian envelope. -/
theorem exists_fixed_canonicalXi_goodHeight_both_horizontalIntegral_bound
    (p : Polynomial Real) :
    exists K k A C : Real,
      0 < K /\ 0 < k /\ 0 < A /\ 0 < C /\
      forall N : Nat, 5 <= N -> exists T : Real,
        (N : Real) <= T /\ T <= N + 1 /\
        (forall sigma,
          sigma ∈ Set.Icc guinandWeilXiContourLeft guinandWeilXiContourRight ->
          riemannXi ((sigma : Complex) + (T : Complex) * Complex.I) ≠ 0) /\
        let bound :=
          C * (abs T + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
              Real.exp (-Real.pi * T ^ 2) *
            xiGoodHeightLogDerivEnvelope K k A N T * (3 / 2 : Real)
        norm
            (guinandWeilHorizontalIntegral
              (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
              guinandWeilXiContourLeft guinandWeilXiContourRight T) <= bound /\
          norm
            (guinandWeilHorizontalIntegral
              (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
              guinandWeilXiContourLeft guinandWeilXiContourRight (-T)) <= bound := by
  obtain ⟨K, k, A, hK, hk, hA, hlogDeriv⟩ :=
    exists_fixed_canonicalXi_goodHeight_global_logDeriv_bound
  obtain ⟨C, hC, hweight⟩ :=
    exists_pos_const_norm_guinandWeilXiContourWeight_horizontal_le p
  refine ⟨K, k, A, C, hK, hk, hA, hC, ?_⟩
  intro N hN
  obtain ⟨T, hTN, hTN1, hlogDerivT⟩ := hlogDeriv N hN
  have hupper := norm_guinandWeilXi_horizontalIntegral_le
    p N T K k A C hC.le
      (fun sigma hsigmaLower hsigmaUpper =>
        hweight sigma T hsigmaLower hsigmaUpper)
      (fun sigma hsigma => (hlogDerivT sigma hsigma).2)
  refine ⟨T, hTN, hTN1,
    (fun sigma hsigma => (hlogDerivT sigma hsigma).1), hupper, ?_⟩
  rw [guinandWeilXi_horizontalIntegral_neg, norm_neg]
  exact hupper

/-- Upper-edge nonvanishing on the fixed strip supplies nonvanishing on the
complete symmetric rectangle boundary.  The lower edge follows from xi
reflection, while the two fixed vertical walls are zero-free independently
of the height. -/
theorem riemannXi_ne_zero_on_symmetric_goodHeight_rectangleBorder
    (T : Real)
    (hupper : forall sigma,
      sigma ∈ Set.Icc guinandWeilXiContourLeft guinandWeilXiContourRight ->
      riemannXi ((sigma : Complex) + (T : Complex) * Complex.I) ≠ 0) :
    ∀ s : Complex, s ∈ guinandWeilRectangleBorder
        ((guinandWeilXiContourLeft : Complex) - (T : Complex) * Complex.I)
        ((guinandWeilXiContourRight : Complex) + (T : Complex) * Complex.I) →
      riemannXi s ≠ 0 := by
  intro s hs
  rcases hs with ((hbottom | hleft) | htop) | hright
  · rw [Complex.mem_reProdIm, Set.uIcc_of_le (by
      norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight]),
      Set.mem_singleton_iff] at hbottom
    norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight] at hbottom
    have hsigma : 1 - s.re ∈
        Set.Icc guinandWeilXiContourLeft guinandWeilXiContourRight := by
      have hre := hbottom.1
      constructor <;>
        norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight] at ⊢ <;>
        linarith
    have hreflected := hupper (1 - s.re) hsigma
    have him : s.im = -T := by
      exact hbottom.2
    have hsform : 1 - s =
        ((1 - s.re : Real) : Complex) + (T : Complex) * Complex.I := by
      apply Complex.ext
      · simp
      · simp [him]
    have honeSub : riemannXi (1 - s) ≠ 0 := by
      simpa only [hsform] using hreflected
    simpa only [riemannXi_one_sub] using honeSub
  · apply riemannXi_ne_zero_of_re_eq_guinandWeilXiContourLeft
    rw [Complex.mem_reProdIm, Set.mem_singleton_iff] at hleft
    norm_num [guinandWeilXiContourLeft] at hleft
    convert hleft.1 using 1 <;> norm_num [guinandWeilXiContourLeft]
  · rw [Complex.mem_reProdIm, Set.uIcc_of_le (by
      norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight]),
      Set.mem_singleton_iff] at htop
    norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight] at htop
    have him : s.im = T := by
      exact htop.2
    have hsform : s =
        (s.re : Complex) + (T : Complex) * Complex.I := by
      apply Complex.ext
      · simp
      · simp [him]
    rw [hsform]
    apply hupper s.re
    constructor
    · norm_num [guinandWeilXiContourLeft] at ⊢
      nlinarith [htop.1.1]
    · simpa [guinandWeilXiContourRight] using htop.1.2
  · apply riemannXi_ne_zero_of_re_eq_guinandWeilXiContourRight
    rw [Complex.mem_reProdIm, Set.mem_singleton_iff] at hright
    norm_num [guinandWeilXiContourRight] at hright
    simpa [guinandWeilXiContourRight] using hright.1

/-- F5 completion: there is an unbounded canonical good-height sequence along
which both horizontal xi contour integrals vanish. -/
theorem exists_canonicalXi_goodHeight_both_horizontalIntegrals_tendsto_zero
    (p : Polynomial Real) :
    exists height : Nat -> Real,
      (∀ᶠ N : Nat in atTop,
        (N : Real) <= height N /\ height N <= N + 1) /\
      (∀ᶠ N : Nat in atTop,
        forall sigma,
          sigma ∈ Set.Icc guinandWeilXiContourLeft guinandWeilXiContourRight ->
          riemannXi
            ((sigma : Complex) + (height N : Complex) * Complex.I) ≠ 0) /\
      Tendsto
        (fun N : Nat =>
          guinandWeilHorizontalIntegral
            (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
            guinandWeilXiContourLeft guinandWeilXiContourRight (height N))
        atTop (nhds 0) /\
      Tendsto
        (fun N : Nat =>
          guinandWeilHorizontalIntegral
            (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
            guinandWeilXiContourLeft guinandWeilXiContourRight (-(height N)))
        atTop (nhds 0) := by
  obtain ⟨K, k, A, C, hK, hk, hA, hC, hbound⟩ :=
    exists_fixed_canonicalXi_goodHeight_both_horizontalIntegral_bound p
  obtain ⟨B, hB, henvelope⟩ :=
    exists_pos_const_xiGoodHeightLogDerivEnvelope_le_pow_four hK hk hA
  let height : Nat -> Real := fun N =>
    if hN : 5 <= N then Classical.choose (hbound N hN) else (N : Real)
  have hheight (N : Nat) (hN : 5 <= N) :
      (N : Real) <= height N /\ height N <= N + 1 /\
      (forall sigma,
        sigma ∈ Set.Icc guinandWeilXiContourLeft guinandWeilXiContourRight ->
        riemannXi
          ((sigma : Complex) + (height N : Complex) * Complex.I) ≠ 0) /\
      let bound :=
        C * (abs (height N) + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
            Real.exp (-Real.pi * (height N) ^ 2) *
          xiGoodHeightLogDerivEnvelope K k A N (height N) * (3 / 2 : Real)
      norm
          (guinandWeilHorizontalIntegral
            (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
            guinandWeilXiContourLeft guinandWeilXiContourRight (height N)) <= bound /\
        norm
          (guinandWeilHorizontalIntegral
            (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
            guinandWeilXiContourLeft guinandWeilXiContourRight (-(height N))) <= bound := by
    dsimp only [height]
    rw [dif_pos hN]
    exact Classical.choose_spec (hbound N hN)
  let M : Nat -> Real := fun N =>
    (C * B * (3 / 2 : Real)) *
      (((N : Real) + 11) ^
          ((guinandWeilPiEvenPolynomial p).natDegree + 4) *
        Real.exp (-Real.pi * (N : Real) ^ 2))
  have hM : Tendsto M atTop (nhds 0) := by
    have h := (tendsto_natCast_add_pow_mul_exp_neg_mul_sq
      ((guinandWeilPiEvenPolynomial p).natDegree + 4)
      (a := 11) (b := Real.pi) (by norm_num) Real.pi_pos).const_mul
        (C * B * (3 / 2 : Real))
    simpa only [M, mul_zero] using h
  have hmajor (N : Nat) (hN : 5 <= N) :
      norm
          (guinandWeilHorizontalIntegral
            (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
            guinandWeilXiContourLeft guinandWeilXiContourRight (height N)) <= M N /\
        norm
          (guinandWeilHorizontalIntegral
            (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
            guinandWeilXiContourLeft guinandWeilXiContourRight (-(height N))) <= M N := by
    obtain ⟨hTN, hTN1, _hnz, hupper, hlower⟩ := hheight N hN
    have hN0 : 0 <= (N : Real) := by positivity
    have hT0 : 0 <= height N := hN0.trans hTN
    have hTX : abs (height N) + 3 <= (N : Real) + 11 := by
      rw [abs_of_nonneg hT0]
      norm_num at hTN1 ⊢
      linarith
    have hpow :
        (abs (height N) + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree <=
          ((N : Real) + 11) ^ (guinandWeilPiEvenPolynomial p).natDegree :=
      pow_le_pow_left₀ (by positivity) hTX _
    have hsquare : (N : Real) ^ 2 <= (height N) ^ 2 := by nlinarith
    have hexp :
        Real.exp (-Real.pi * (height N) ^ 2) <=
          Real.exp (-Real.pi * (N : Real) ^ 2) := by
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have henv := henvelope N (height N) hN hTN hTN1
    have henv0 : 0 <= xiGoodHeightLogDerivEnvelope K k A N (height N) := by
      have hlog0 : 0 <=
          Real.log (xiLocalDiskGrowthFactor K k A (height N) 4) :=
        Real.log_nonneg
          (one_lt_xiLocalDiskGrowthFactor hK hk hA (by norm_num)).le
      have hcount0 :=
        canonicalPositiveOrdinateZetaZeroMultiplicityCount_nonneg ((N : Real) + 5)
      unfold xiGoodHeightLogDerivEnvelope
      positivity
    have hscalar :
        C * (abs (height N) + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
              Real.exp (-Real.pi * (height N) ^ 2) *
            xiGoodHeightLogDerivEnvelope K k A N (height N) * (3 / 2 : Real) <=
          M N := by
      calc
        C * (abs (height N) + 3) ^ (guinandWeilPiEvenPolynomial p).natDegree *
              Real.exp (-Real.pi * (height N) ^ 2) *
            xiGoodHeightLogDerivEnvelope K k A N (height N) * (3 / 2 : Real) <=
            C * ((N : Real) + 11) ^ (guinandWeilPiEvenPolynomial p).natDegree *
              Real.exp (-Real.pi * (N : Real) ^ 2) *
            (B * ((N : Real) + 11) ^ 4) * (3 / 2 : Real) := by
          gcongr
        _ = M N := by
          dsimp only [M]
          rw [pow_add]
          ring
    exact ⟨hupper.trans hscalar, hlower.trans hscalar⟩
  refine ⟨height, ?_, ?_, ?_, ?_⟩
  · filter_upwards [eventually_atTop.2 ⟨5, fun _ hN => hN⟩] with N hN
    exact ⟨(hheight N hN).1, (hheight N hN).2.1⟩
  · filter_upwards [eventually_atTop.2 ⟨5, fun _ hN => hN⟩] with N hN
    exact (hheight N hN).2.2.1
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero'
      (Eventually.of_forall fun N => norm_nonneg _)
      (by
        filter_upwards [eventually_atTop.2 ⟨5, fun _ hN => hN⟩] with N hN
        exact (hmajor N hN).1)
      hM
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero'
      (Eventually.of_forall fun N => norm_nonneg _)
      (by
        filter_upwards [eventually_atTop.2 ⟨5, fun _ hN => hN⟩] with N hN
        exact (hmajor N hN).2)
      hM

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
