import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Convex
import RiemannHypothesisProject.RiemannVonMangoldt.ZModTwoHalfTail

/-!
# Analytic continuation of the mod-2 regularized half-tail

This module proves the nonendpoint Hurwitz comparison directly.  The
regularized complex-power differences gain one power, so their series is
locally uniformly convergent on `0 < re s`.  Analytic continuation from the
ordinary Hurwitz-series region `1 < re s` then identifies its sum with the
corresponding difference of Hurwitz zeta values.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Filter MeasureTheory

open scoped Topology

noncomputable section

/-- The complex-parameter version of one mod-2 regularized half-tail term. -/
noncomputable def zmodTwoRegularizedHalfTailComplexTerm
    (s : Complex) (m : Nat) : Complex :=
  (((m : Real) + (1 : Real) / 2 : Real) : Complex) ^ (-s) -
    (((m + 1 : Nat) : Complex) ^ (-s))

/-- On the positive real axis, the complex-parameter term is the existing term. -/
theorem zmodTwoRegularizedHalfTailComplexTerm_ofReal
    (x : Real) (m : Nat) :
    zmodTwoRegularizedHalfTailComplexTerm (x : Complex) m =
      zmodTwoRegularizedHalfTailTerm x m := by
  simp [zmodTwoRegularizedHalfTailComplexTerm,
    zmodTwoRegularizedHalfTailTerm]

/--
Complex-parameter mean-value bound for a positive-real power difference.

The gain of one power is uniform in the imaginary part: only `norm s` enters
the constant, while decay is governed by `re s`.
-/
theorem norm_ofReal_cpow_neg_sub_le_of_re_pos
    {s : Complex} {a b : Real} (hs : 0 < s.re) (ha : 1 <= a)
    (hab : a <= b) :
    norm ((b : Complex) ^ (-s) - (a : Complex) ^ (-s)) <=
      norm s * a ^ (-s.re - 1) * norm (b - a) := by
  let f : Real -> Complex := fun t => (t : Complex) ^ (-s)
  have hs_ne : -s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have ha_pos : 0 < a := zero_lt_one.trans_le ha
  have hf : forall t, t ∈ Set.Icc a b -> DifferentiableAt Real f t := by
    intro t ht
    exact differentiableAt_id.ofReal_cpow_const
      ((ha_pos.trans_le ht.1).ne') hs_ne
  have hbound : forall t, t ∈ Set.Icc a b ->
      norm (deriv f t) <= norm s * a ^ (-s.re - 1) := by
    intro t ht
    have ht_pos : 0 < t := ha_pos.trans_le ht.1
    rw [Complex.deriv_ofReal_cpow_const ht_pos.ne' hs_ne]
    have hpow_norm :
        norm ((t : Complex) ^ (-s - 1)) = t ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
      simp
    calc
      norm (-s * (t : Complex) ^ (-s - 1)) =
          norm s * t ^ (-s.re - 1) := by
            rw [norm_mul, norm_neg, hpow_norm]
      _ <= norm s * a ^ (-s.re - 1) := by
            exact mul_le_mul_of_nonneg_left
              ((Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
                (by linarith : -s.re - 1 <= 0))
                ha_pos ht_pos ht.1)
              (norm_nonneg s)
  have hmean :=
    (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
      (f := f) hf hbound
      ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  simpa [f, mul_assoc] using hmean

/-- The complex regularized terms are norm-summable throughout `0 < re s`. -/
theorem summable_norm_zmodTwoRegularizedHalfTailComplexTerm
    {s : Complex} (hs : 0 < s.re) :
    Summable fun m : Nat => norm (zmodTwoRegularizedHalfTailComplexTerm s m) := by
  have hshift :
      Summable fun n : Nat =>
        1 / |(n : Real) + (3 : Real) / 2| ^ (s.re + 1) :=
    (Real.summable_one_div_nat_add_rpow
      ((3 : Real) / 2) (s.re + 1)).mpr (by linarith)
  have hcore :
      Summable fun n : Nat =>
        ((n : Real) + (3 : Real) / 2) ^ (-s.re - 1) := by
    refine hshift.congr ?_
    intro n
    have hbase_pos : 0 < (n : Real) + (3 : Real) / 2 := by positivity
    rw [abs_of_pos hbase_pos, show -s.re - 1 = -(s.re + 1) by ring,
      Real.rpow_neg hbase_pos.le]
    simp [one_div]
  have hmajor :
      Summable fun n : Nat =>
        norm s * ((n : Real) + (3 : Real) / 2) ^ (-s.re - 1) :=
    hcore.mul_left (norm s)
  have htail :
      Summable fun n : Nat =>
        norm (zmodTwoRegularizedHalfTailComplexTerm s (n + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hmajor
    intro n
    let a : Real := ((n + 1 : Nat) : Real) + (1 : Real) / 2
    let b : Real := ((n + 2 : Nat) : Real)
    have ha : 1 <= a := by
      have hn : 0 <= (n : Real) := Nat.cast_nonneg n
      dsimp [a]
      push_cast
      linarith
    have hab : a <= b := by
      have hn : 0 <= (n : Real) := Nat.cast_nonneg n
      dsimp [a, b]
      push_cast
      linarith
    have hdist : norm (b - a) <= (1 : Real) := by
      have hdiff : b - a = (1 : Real) / 2 := by
        dsimp [a, b]
        push_cast
        ring
      rw [hdiff, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
      norm_num
    have ha_eq : a = (n : Real) + (3 : Real) / 2 := by
      dsimp [a]
      push_cast
      ring
    have hmean := norm_ofReal_cpow_neg_sub_le_of_re_pos hs ha hab
    calc
      norm (zmodTwoRegularizedHalfTailComplexTerm s (n + 1)) =
          norm ((b : Complex) ^ (-s) - (a : Complex) ^ (-s)) := by
            rw [zmodTwoRegularizedHalfTailComplexTerm,
              show n + 1 + 1 = n + 2 by omega, norm_sub_rev]
            simp [a, b]
      _ <= norm s * a ^ (-s.re - 1) * norm (b - a) := hmean
      _ <= norm s * a ^ (-s.re - 1) * 1 := by
            exact mul_le_mul_of_nonneg_left hdist
              (mul_nonneg (norm_nonneg s) (Real.rpow_nonneg (by positivity) _))
      _ = norm s * ((n : Real) + (3 : Real) / 2) ^ (-s.re - 1) := by
            rw [mul_one, ha_eq]
  exact (summable_nat_add_iff (f := fun m : Nat =>
    norm (zmodTwoRegularizedHalfTailComplexTerm s m)) 1).mp (by
      simpa [Nat.add_comm] using htail)

/-- The complex regularized half-tail is summable on the open right half-plane. -/
theorem summable_zmodTwoRegularizedHalfTailComplexTerm
    {s : Complex} (hs : 0 < s.re) :
    Summable (zmodTwoRegularizedHalfTailComplexTerm s) := by
  rw [<- summable_norm_iff]
  exact summable_norm_zmodTwoRegularizedHalfTailComplexTerm hs

/--
The holomorphic presentation separates the first term from the uniformly
summable shifted tail.
-/
noncomputable def zmodTwoRegularizedHalfTailAnalyticValue
    (s : Complex) : Complex :=
  zmodTwoRegularizedHalfTailComplexTerm s 0 +
    ∑' n : Nat, zmodTwoRegularizedHalfTailComplexTerm s (n + 1)

/-- The holomorphic presentation equals the ordinary tsum where `0 < re s`. -/
theorem zmodTwoRegularizedHalfTailAnalyticValue_eq_tsum
    {s : Complex} (hs : 0 < s.re) :
    zmodTwoRegularizedHalfTailAnalyticValue s =
      ∑' m : Nat, zmodTwoRegularizedHalfTailComplexTerm s m := by
  rw [zmodTwoRegularizedHalfTailAnalyticValue,
    (summable_zmodTwoRegularizedHalfTailComplexTerm hs).tsum_eq_zero_add]

/-- Each complex-parameter regularized term is entire in the parameter. -/
theorem differentiable_zmodTwoRegularizedHalfTailComplexTerm (m : Nat) :
    Differentiable Complex fun s : Complex =>
      zmodTwoRegularizedHalfTailComplexTerm s m := by
  apply Differentiable.sub
  · exact differentiable_neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  · exact differentiable_neg.const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)))

/-- The shifted regularized tail is holomorphic at every point with positive real part. -/
theorem differentiableAt_zmodTwoRegularizedHalfTailAnalyticTail
    {s : Complex} (hs : 0 < s.re) :
    DifferentiableAt Complex
      (fun z : Complex =>
        ∑' n : Nat, zmodTwoRegularizedHalfTailComplexTerm z (n + 1)) s := by
  let y : Real := s.re / 2
  let B : Real := norm s + 1
  let U : Set Complex := {z : Complex | y < z.re ∧ norm z < B}
  have hy : 0 < y := by dsimp [y]; linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hU_open : IsOpen U := by
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := by
    constructor
    · dsimp [y]
      linarith
    · dsimp [B]
      linarith
  have hshift :
      Summable fun n : Nat =>
        1 / |(n : Real) + (3 : Real) / 2| ^ (y + 1) :=
    (Real.summable_one_div_nat_add_rpow
      ((3 : Real) / 2) (y + 1)).mpr (by linarith)
  have hcore :
      Summable fun n : Nat =>
        ((n : Real) + (3 : Real) / 2) ^ (-y - 1) := by
    refine hshift.congr ?_
    intro n
    have hbase_pos : 0 < (n : Real) + (3 : Real) / 2 := by positivity
    rw [abs_of_pos hbase_pos, show -y - 1 = -(y + 1) by ring,
      Real.rpow_neg hbase_pos.le]
    simp [one_div]
  have hmajor :
      Summable fun n : Nat =>
        B * ((n : Real) + (3 : Real) / 2) ^ (-y - 1) :=
    hcore.mul_left B
  have hdiff : forall n : Nat,
      DifferentiableOn Complex
        (fun z : Complex => zmodTwoRegularizedHalfTailComplexTerm z (n + 1)) U := by
    intro n
    exact (differentiable_zmodTwoRegularizedHalfTailComplexTerm (n + 1)).differentiableOn
  have hbound : forall (n : Nat) (z : Complex), z ∈ U ->
      norm (zmodTwoRegularizedHalfTailComplexTerm z (n + 1)) <=
        B * ((n : Real) + (3 : Real) / 2) ^ (-y - 1) := by
    intro n z hz
    let a : Real := ((n + 1 : Nat) : Real) + (1 : Real) / 2
    let b : Real := ((n + 2 : Nat) : Real)
    have hz_re : 0 < z.re := hy.trans hz.1
    have ha : 1 <= a := by
      have hn : 0 <= (n : Real) := Nat.cast_nonneg n
      dsimp [a]
      push_cast
      linarith
    have hab : a <= b := by
      have hn : 0 <= (n : Real) := Nat.cast_nonneg n
      dsimp [a, b]
      push_cast
      linarith
    have hdist : norm (b - a) <= (1 : Real) := by
      have hdiff : b - a = (1 : Real) / 2 := by
        dsimp [a, b]
        push_cast
        ring
      rw [hdiff, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
      norm_num
    have hmean := norm_ofReal_cpow_neg_sub_le_of_re_pos hz_re ha hab
    have ha_pos : 0 < a := zero_lt_one.trans_le ha
    have ha_one : 1 <= a := ha
    have hexp : a ^ (-z.re - 1) <= a ^ (-y - 1) := by
      have hyz : y < z.re := hz.1
      exact Real.rpow_le_rpow_of_exponent_le ha_one (by linarith)
    have ha_eq : a = (n : Real) + (3 : Real) / 2 := by
      dsimp [a]
      push_cast
      ring
    calc
      norm (zmodTwoRegularizedHalfTailComplexTerm z (n + 1)) =
          norm ((b : Complex) ^ (-z) - (a : Complex) ^ (-z)) := by
            rw [zmodTwoRegularizedHalfTailComplexTerm,
              show n + 1 + 1 = n + 2 by omega, norm_sub_rev]
            simp [a, b]
      _ <= norm z * a ^ (-z.re - 1) * norm (b - a) := hmean
      _ <= norm z * a ^ (-z.re - 1) * 1 := by
            exact mul_le_mul_of_nonneg_left hdist
              (mul_nonneg (norm_nonneg z) (Real.rpow_nonneg ha_pos.le _))
      _ = norm z * a ^ (-z.re - 1) := by ring
      _ <= B * a ^ (-y - 1) := by
            calc
              norm z * a ^ (-z.re - 1) <=
                  B * a ^ (-z.re - 1) :=
                mul_le_mul_of_nonneg_right hz.2.le
                  (Real.rpow_nonneg ha_pos.le _)
              _ <= B * a ^ (-y - 1) :=
                mul_le_mul_of_nonneg_left hexp hB.le
      _ = B * ((n : Real) + (3 : Real) / 2) ^ (-y - 1) := by
            rw [ha_eq]
  have hdiffU := Complex.differentiableOn_tsum_of_summable_norm
    hmajor hdiff hU_open hbound
  exact hdiffU.differentiableAt (hU_open.mem_nhds hsU)

/-- The regularized half-tail analytic value is holomorphic on `0 < re s`. -/
theorem differentiableOn_zmodTwoRegularizedHalfTailAnalyticValue :
    DifferentiableOn Complex zmodTwoRegularizedHalfTailAnalyticValue
      {s : Complex | 0 < s.re} := by
  intro s hs
  exact
    ((differentiable_zmodTwoRegularizedHalfTailComplexTerm 0 s).add
      (differentiableAt_zmodTwoRegularizedHalfTailAnalyticTail hs)).differentiableWithinAt

/-- In the absolute-convergence region, the regularized sum is the Hurwitz difference. -/
theorem zmodTwoRegularizedHalfTailAnalyticValue_eq_hurwitzSub_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    zmodTwoRegularizedHalfTailAnalyticValue s =
      HurwitzZeta.hurwitzZeta
          (((1 : Real) / 2 : Real) : UnitAddCircle) s -
        HurwitzZeta.hurwitzZeta ((1 : Real) : UnitAddCircle) s := by
  have hhalf := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
    (a := (1 : Real) / 2) (by constructor <;> norm_num) hs
  have hone := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
    (a := (1 : Real)) (by constructor <;> norm_num) hs
  have hsub := hhalf.sub hone
  have hterms : HasSum (zmodTwoRegularizedHalfTailComplexTerm s)
      (HurwitzZeta.hurwitzZeta
          (((1 : Real) / 2 : Real) : UnitAddCircle) s -
        HurwitzZeta.hurwitzZeta ((1 : Real) : UnitAddCircle) s) := by
    refine hsub.congr_fun ?_
    intro n
    simp [zmodTwoRegularizedHalfTailComplexTerm, div_eq_mul_inv,
      <- Complex.cpow_neg, Complex.ofReal_add]
  rw [zmodTwoRegularizedHalfTailAnalyticValue_eq_tsum (lt_trans zero_lt_one hs)]
  exact hterms.tsum_eq

/--
Analytic continuation of the regularized half-tail identity to the full open
right half-plane.
-/
theorem zmodTwoRegularizedHalfTailAnalyticValue_eq_hurwitzSub_of_re_pos
    {s : Complex} (hs : 0 < s.re) :
    zmodTwoRegularizedHalfTailAnalyticValue s =
      HurwitzZeta.hurwitzZeta
          (((1 : Real) / 2 : Real) : UnitAddCircle) s -
        HurwitzZeta.hurwitzZeta ((1 : Real) : UnitAddCircle) s := by
  let U : Set Complex := {z : Complex | 0 < z.re}
  let f : Complex -> Complex := zmodTwoRegularizedHalfTailAnalyticValue
  let g : Complex -> Complex := fun z =>
    HurwitzZeta.hurwitzZeta
        (((1 : Real) / 2 : Real) : UnitAddCircle) z -
      HurwitzZeta.hurwitzZeta ((1 : Real) : UnitAddCircle) z
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd Complex f U := by
    exact DifferentiableOn.analyticOnNhd
      differentiableOn_zmodTwoRegularizedHalfTailAnalyticValue hU_open
  have hg : AnalyticOnNhd Complex g U := by
    exact DifferentiableOn.analyticOnNhd
      (HurwitzZeta.differentiable_hurwitzZeta_sub_hurwitzZeta
        (((1 : Real) / 2 : Real) : UnitAddCircle)
        ((1 : Real) : UnitAddCircle)).differentiableOn hU_open
  have hU_preconnected : IsPreconnected U := by
    exact (convex_halfSpace_re_gt 0).isPreconnected
  have htwo_mem : (2 : Complex) ∈ U := by simp [U]
  have hs_mem : s ∈ U := by simpa [U] using hs
  have hV : {z : Complex | 1 < z.re} ∈ nhds (2 : Complex) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hfg : f =ᶠ[nhds (2 : Complex)] g := by
    filter_upwards [hV] with z hz
    exact zmodTwoRegularizedHalfTailAnalyticValue_eq_hurwitzSub_of_one_lt_re hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hU_preconnected
    htwo_mem hfg hs_mem

/-- The ordinary complex regularized tsum equals the Hurwitz difference on `0 < re s`. -/
theorem zmodTwoRegularizedHalfTailComplex_tsum_eq_hurwitzSub_of_re_pos
    {s : Complex} (hs : 0 < s.re) :
    (∑' m : Nat, zmodTwoRegularizedHalfTailComplexTerm s m) =
      HurwitzZeta.hurwitzZeta
          (((1 : Real) / 2 : Real) : UnitAddCircle) s -
        HurwitzZeta.hurwitzZeta ((1 : Real) : UnitAddCircle) s := by
  rw [<- zmodTwoRegularizedHalfTailAnalyticValue_eq_tsum hs]
  exact zmodTwoRegularizedHalfTailAnalyticValue_eq_hurwitzSub_of_re_pos hs

/--
The previously isolated mod-2 regularized half-tail/Hurwitz source theorem.
It actually holds on the whole positive real axis, stronger than the required
open-unit-interval statement.
-/
theorem zmodTwoRegularizedHalfTail_tsum_eq_hurwitzSub_of_pos
    {x : Real} (hx : 0 < x) :
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) =
      HurwitzZeta.hurwitzZeta
          (((1 : Real) / 2 : Real) : UnitAddCircle) (x : Complex) -
        HurwitzZeta.hurwitzZeta
          ((1 : Real) : UnitAddCircle) (x : Complex) := by
  calc
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) =
        ∑' m : Nat, zmodTwoRegularizedHalfTailComplexTerm (x : Complex) m := by
          apply tsum_congr
          intro m
          exact (zmodTwoRegularizedHalfTailComplexTerm_ofReal x m).symm
    _ = HurwitzZeta.hurwitzZeta
          (((1 : Real) / 2 : Real) : UnitAddCircle) (x : Complex) -
        HurwitzZeta.hurwitzZeta
          ((1 : Real) : UnitAddCircle) (x : Complex) :=
      zmodTwoRegularizedHalfTailComplex_tsum_eq_hurwitzSub_of_re_pos
        (by simpa using hx)

/-- The isolated 90% source theorem is now discharged without hypotheses. -/
theorem zmodTwoRegularizedHalfTailHurwitzFormula :
    ZModTwoRegularizedHalfTailHurwitzFormula := by
  intro x hx _hx_lt_one
  exact zmodTwoRegularizedHalfTail_tsum_eq_hurwitzSub_of_pos hx

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
