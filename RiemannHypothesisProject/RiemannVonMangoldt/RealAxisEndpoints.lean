import RiemannHypothesisProject.RiemannVonMangoldt.AxisWindows
import RiemannHypothesisProject.RiemannVonMangoldt.OpenUnitIntervalZetaEndpoints

/-!
# Real-axis endpoint consequences for Riemann-von-Mangoldt cleanup

This module contains the endpoint implications from open-unit-interval
zero-freeness and checked `ZMod`/Hurwitz-tail inputs to the residual real-axis
axis-count bounds used by the closed-ball Riemann-von-Mangoldt route.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Asymptotics Filter MeasureTheory

open scoped ComplexConjugate Topology

noncomputable section
/--
Every real zeta zero with nonpositive real part is a project-known trivial
zero.

The proof uses Mathlib's functional equation for `riemannZeta`, the
nonvanishing theorem on `re > 1`, nonvanishing of `Gamma` on positive real
part, and the real cosine zero classification.
-/
theorem isTrivialZetaZero_of_isZetaZero_of_im_eq_zero_of_re_nonpos
    {s : Complex} (hz : IsZetaZero s) (haxis : Complex.im s = 0)
    (hre_nonpos : s.re <= 0) :
    IsTrivialZetaZero s := by
  let x : Real := s.re
  have hs_eq : s = (x : Complex) :=
    Complex.ext (by change s.re = x; rfl) (by change s.im = 0; exact haxis)
  have hx_nonpos : x <= 0 := by simpa [x] using hre_nonpos
  rcases lt_or_eq_of_le hx_nonpos with hx_neg | hx_zero
  case inl =>
    let u : Real := 1 - x
    have hu_gt_one : 1 < u := by
      dsimp [u]
      linarith
    have hzero_left : riemannZeta (1 - (u : Complex)) = 0 := by
      have hsu : 1 - (u : Complex) = s := by
        rw [hs_eq]
        apply Complex.ext <;> simp [u]
      simpa [hsu, IsZetaZero] using hz
    have hu_not_neg_nat : forall n : Nat,
        Not ((u : Complex) = -((n : Complex))) := by
      intro n h
      have hre : u = -(n : Real) := by
        have h_re := congrArg Complex.re h
        simpa using h_re
      have hbad : (0 : Real) < 0 := by
        have hn_nonneg : (0 : Real) <= n := by positivity
        linarith
      exact (lt_irrefl (0 : Real)) hbad
    have hu_ne_one : Not ((u : Complex) = 1) := by
      intro h
      have hu_eq : u = 1 := by
        have h_re := congrArg Complex.re h
        simpa using h_re
      linarith
    have hfe :=
      riemannZeta_one_sub (s := (u : Complex)) hu_not_neg_nat hu_ne_one
    have hprod_zero :
        2 * (2 * (Real.pi : Complex)) ^ (-(u : Complex)) *
            Complex.Gamma (u : Complex) *
              Complex.cos ((Real.pi : Complex) * (u : Complex) / 2) *
                riemannZeta (u : Complex) = 0 := by
      have htmp := hzero_left
      rw [hfe] at htmp
      exact htmp
    have htwo_ne : Not ((2 : Complex) = 0) := by norm_num
    have hbase_ne : Not (2 * (Real.pi : Complex) = 0) := by
      norm_num [Real.pi_ne_zero]
    have hpow_ne :
        Not ((2 * (Real.pi : Complex)) ^ (-(u : Complex)) = 0) := by
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl hbase_ne)
    have hgamma_ne : Not (Complex.Gamma (u : Complex) = 0) := by
      exact
        Complex.Gamma_ne_zero_of_re_pos
          (by simpa using (lt_trans zero_lt_one hu_gt_one))
    have hzeta_u_ne : Not (riemannZeta (u : Complex) = 0) := by
      exact riemannZeta_ne_zero_of_one_lt_re (by simpa using hu_gt_one)
    have hcos_zero :
        Complex.cos ((Real.pi : Complex) * (u : Complex) / 2) = 0 := by
      match mul_eq_zero.mp hprod_zero with
      | Or.inr hzeta_zero => exact False.elim (hzeta_u_ne hzeta_zero)
      | Or.inl hprefix_zero =>
        match mul_eq_zero.mp hprefix_zero with
        | Or.inr hcos_zero => exact hcos_zero
        | Or.inl hprefix_zero =>
          match mul_eq_zero.mp hprefix_zero with
          | Or.inr hgamma_zero => exact False.elim (hgamma_ne hgamma_zero)
          | Or.inl hprefix_zero =>
            match mul_eq_zero.mp hprefix_zero with
            | Or.inr hpow_zero => exact False.elim (hpow_ne hpow_zero)
            | Or.inl htwo_zero => exact False.elim (htwo_ne htwo_zero)
    have hreal_cos_zero : Real.cos (Real.pi * u / 2) = 0 := by
      have hcast : ((Real.cos (Real.pi * u / 2) : Real) : Complex) = 0 := by
        simpa [Complex.ofReal_cos] using hcos_zero
      exact Complex.ofReal_eq_zero.mp hcast
    let k : Int :=
      Classical.choose (Real.cos_eq_zero_iff.mp hreal_cos_zero)
    have hktheta :
        Real.pi * u / 2 = (2 * (k : Real) + 1) * Real.pi / 2 := by
      exact Classical.choose_spec (Real.cos_eq_zero_iff.mp hreal_cos_zero)
    have hu_eq : u = 2 * (k : Real) + 1 := by
      nlinarith [Real.pi_pos]
    have hk_pos_real : 0 < (k : Real) := by
      nlinarith
    have hk_pos_int : 0 < k := by
      exact_mod_cast hk_pos_real
    let n : Nat := k.toNat - 1
    have hn_int : ((n : Nat) : Int) = k - 1 := by
      simpa [n] using Int.toNat_pred_coe_of_pos hk_pos_int
    have hk_int : k = (n : Int) + 1 := by
      omega
    refine Exists.intro n ?_
    rw [hs_eq]
    exact Complex.ext
      (by
        have hx_eq : x = -2 * ((n : Real) + 1) := by
          have hk_real : (k : Real) = (n : Real) + 1 := by
            exact_mod_cast hk_int
          dsimp [u] at hu_eq
          nlinarith
        simp [hx_eq])
      (by simp)
  case inr =>
    have hs_zero : s = 0 := by
      rw [hs_eq]
      apply Complex.ext <;> simp [x, hx_zero]
    have hz0 : riemannZeta (0 : Complex) = 0 := by
      simpa [hs_zero, IsZetaZero] using hz
    have hnonzero : Not (riemannZeta (0 : Complex) = 0) := by
      norm_num [riemannZeta_zero]
    exact False.elim (hnonzero hz0)

/--
Every zeta zero in the open left half-plane is one of the project-known
trivial zeroes.

This is the complex version of the functional-equation argument used above on
the real axis.  Reflecting `s` to `u = 1 - s` moves it into `re u > 1`; the
nonvanishing of `zeta` and `Gamma` there forces the cosine factor in Mathlib's
functional equation to vanish.  Mathlib's complex cosine zero classification
then places `u` at a positive odd integer, hence `s` at a negative even
integer.
-/
theorem isTrivialZetaZero_of_isZetaZero_of_re_neg
    {s : Complex} (hz : IsZetaZero s) (hre_neg : s.re < 0) :
    IsTrivialZetaZero s := by
  let u : Complex := 1 - s
  have hu_gt_one : 1 < u.re := by
    have hu_re : u.re = 1 - s.re := by
      dsimp [u]
    linarith
  have hzero_left : riemannZeta (1 - u) = 0 := by
    have hsu : 1 - u = s := by
      dsimp [u]
      ring
    simpa [hsu, IsZetaZero] using hz
  have hu_not_neg_nat : forall n : Nat,
      Not (u = -((n : Complex))) := by
    intro n h
    have hre : u.re = -(n : Real) := by
      have h_re := congrArg Complex.re h
      simpa using h_re
    have hn_nonneg : (0 : Real) <= n := by positivity
    linarith
  have hu_ne_one : Not (u = 1) := by
    intro h
    have hu_eq : u.re = 1 := by
      have h_re := congrArg Complex.re h
      simpa using h_re
    linarith
  have hfe := riemannZeta_one_sub (s := u) hu_not_neg_nat hu_ne_one
  have hprod_zero :
      2 * (2 * (Real.pi : Complex)) ^ (-u) *
          Complex.Gamma u *
            Complex.cos ((Real.pi : Complex) * u / 2) *
              riemannZeta u = 0 := by
    have htmp := hzero_left
    rw [hfe] at htmp
    exact htmp
  have htwo_ne : Not ((2 : Complex) = 0) := by norm_num
  have hbase_ne : Not (2 * (Real.pi : Complex) = 0) := by
    norm_num [Real.pi_ne_zero]
  have hpow_ne : Not ((2 * (Real.pi : Complex)) ^ (-u) = 0) := by
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hbase_ne)
  have hgamma_ne : Not (Complex.Gamma u = 0) := by
    exact
      Complex.Gamma_ne_zero_of_re_pos
        (by linarith [hu_gt_one])
  have hzeta_u_ne : Not (riemannZeta u = 0) := by
    exact riemannZeta_ne_zero_of_one_lt_re hu_gt_one
  have hcos_zero :
      Complex.cos ((Real.pi : Complex) * u / 2) = 0 := by
    match mul_eq_zero.mp hprod_zero with
    | Or.inr hzeta_zero => exact False.elim (hzeta_u_ne hzeta_zero)
    | Or.inl hprefix_zero =>
      match mul_eq_zero.mp hprefix_zero with
      | Or.inr hcos_zero => exact hcos_zero
      | Or.inl hprefix_zero =>
        match mul_eq_zero.mp hprefix_zero with
        | Or.inr hgamma_zero => exact False.elim (hgamma_ne hgamma_zero)
        | Or.inl hprefix_zero =>
          match mul_eq_zero.mp hprefix_zero with
          | Or.inr hpow_zero => exact False.elim (hpow_ne hpow_zero)
          | Or.inl htwo_zero => exact False.elim (htwo_ne htwo_zero)
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos_zero
  have htheta :
      (Real.pi : Complex) * u / 2 =
        (2 * (k : Complex) + 1) * (Real.pi : Complex) / 2 := by
    simpa using hk
  have hu_eq : u = 2 * (k : Complex) + 1 := by
    have htwice := congrArg (fun z : Complex => z * 2) htheta
    have htmp :
        u = 2 * (((k : Complex) * 2 + 1) * (2 : Complex)⁻¹) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htwice
    calc
      u = 2 * (((k : Complex) * 2 + 1) * (2 : Complex)⁻¹) := htmp
      _ = 2 * (k : Complex) + 1 := by ring
  have hu_re_eq : u.re = 2 * (k : Real) + 1 := by
    have h_re := congrArg Complex.re hu_eq
    simpa using h_re
  have hk_pos_real : 0 < (k : Real) := by
    linarith
  have hk_pos_int : 0 < k := by
    exact_mod_cast hk_pos_real
  let n : Nat := k.toNat - 1
  have hn_int : ((n : Nat) : Int) = k - 1 := by
    simpa [n] using Int.toNat_pred_coe_of_pos hk_pos_int
  have hk_int : k = (n : Int) + 1 := by
    omega
  refine Exists.intro n ?_
  have hk_complex : (k : Complex) = (n : Complex) + 1 := by
    exact_mod_cast hk_int
  have hs_eq : s = 1 - u := by
    dsimp [u]
    ring
  calc
    s = 1 - u := hs_eq
    _ = 1 - (2 * (k : Complex) + 1) := by rw [hu_eq]
    _ = -2 * ((n : Complex) + 1) := by
      rw [hk_complex]
      ring

/-- The checked nonpositive real-axis theorem as a packaged source target. -/
theorem nonpositiveRealAxisZetaZeroClassification :
    forall s : Complex,
      IsZetaZero s ->
        Complex.im s = 0 ->
          s.re <= 0 ->
            IsTrivialZetaZero s := by
  intro s hz haxis hre_nonpos
  exact
    isTrivialZetaZero_of_isZetaZero_of_im_eq_zero_of_re_nonpos
      hz haxis hre_nonpos

/--
To prove the full left-real-axis classification it remains only to rule out
real zeta zeroes in the open interval `(0, 1)`.
-/
theorem leftRealAxisZetaZeroClassification_of_openUnitIntervalRealAxisZetaZeroFree
    (hopen : OpenUnitIntervalRealAxisZetaZeroFree) :
    LeftRealAxisZetaZeroClassification := by
  intro s hz haxis hre_lt_one
  by_cases hre_nonpos : s.re <= 0
  · exact
      isTrivialZetaZero_of_isZetaZero_of_im_eq_zero_of_re_nonpos
        hz haxis hre_nonpos
  · exact False.elim
      (hopen s hz haxis (lt_of_not_ge hre_nonpos) hre_lt_one)

/-- Full real-axis classification implies the left-half-plane version. -/
theorem leftRealAxisZetaZeroClassification_of_realAxisZetaZeroClassification
    (hrealAxis : RealAxisZetaZeroClassification) :
    LeftRealAxisZetaZeroClassification := by
  intro s hz haxis _hre
  exact hrealAxis s hz haxis

/--
The left-half-plane real-axis classification implies the full real-axis
classification, because zeta has no zero with `1 <= re s`.
-/
theorem realAxisZetaZeroClassification_of_leftRealAxisZetaZeroClassification
    (hleft : LeftRealAxisZetaZeroClassification) :
    RealAxisZetaZeroClassification := by
  intro s hz haxis
  have hre_lt : s.re < 1 := by
    by_contra hnot
    exact not_isZetaZero_of_one_le_re (le_of_not_gt hnot) hz
  exact hleft s hz haxis hre_lt

/-- The two real-axis classification targets are equivalent. -/
theorem realAxisZetaZeroClassification_iff_leftRealAxisZetaZeroClassification :
    RealAxisZetaZeroClassification ↔ LeftRealAxisZetaZeroClassification := by
  constructor
  · exact leftRealAxisZetaZeroClassification_of_realAxisZetaZeroClassification
  · exact realAxisZetaZeroClassification_of_leftRealAxisZetaZeroClassification

/--
The classical real-axis zero classification discharges the project residual
axis target.
-/
theorem noResidualRealAxisZetaZeros_of_realAxisZetaZeroClassification
    (hrealAxis : RealAxisZetaZeroClassification) :
    NoResidualRealAxisZetaZeros := by
  intro rho haxis
  apply hrealAxis (rho : Complex)
  · unfold IsZetaZero
    exact mem_riemannZetaZeros.mp rho.property
  · exact haxis

/--
The sharpened left-half-plane classification also discharges the project
residual axis target; the excluded right half-plane is handled by zeta
nonvanishing.
-/
theorem noResidualRealAxisZetaZeros_of_leftRealAxisZetaZeroClassification
    (hleft : LeftRealAxisZetaZeroClassification) :
    NoResidualRealAxisZetaZeros :=
  noResidualRealAxisZetaZeros_of_realAxisZetaZeroClassification
    (realAxisZetaZeroClassification_of_leftRealAxisZetaZeroClassification
      hleft)

/--
The residual axis windows are empty once the only remaining real-axis gap,
zero-freeness on `(0, 1)`, is supplied.
-/
theorem noResidualRealAxisZetaZeros_of_openUnitIntervalRealAxisZetaZeroFree
    (hopen : OpenUnitIntervalRealAxisZetaZeroFree) :
    NoResidualRealAxisZetaZeros :=
  noResidualRealAxisZetaZeros_of_leftRealAxisZetaZeroClassification
    (leftRealAxisZetaZeroClassification_of_openUnitIntervalRealAxisZetaZeroFree
      hopen)

/-- The eta formula on `(0, 1)` discharges the project residual axis target. -/
theorem noResidualRealAxisZetaZeros_of_etaFormula
    (hetaFormula : OpenUnitIntervalRiemannZetaEtaFormula) :
    NoResidualRealAxisZetaZeros :=
  noResidualRealAxisZetaZeros_of_openUnitIntervalRealAxisZetaZeroFree
    (openUnitIntervalRealAxisZetaZeroFree_of_etaFormula hetaFormula)

/-- The canonical eta formula on `(0, 1)` discharges the project residual axis target. -/
theorem noResidualRealAxisZetaZeros_of_etaValueFormula
    (hetaValueFormula : OpenUnitIntervalRiemannZetaEtaValueFormula) :
    NoResidualRealAxisZetaZeros :=
  noResidualRealAxisZetaZeros_of_openUnitIntervalRealAxisZetaZeroFree
    (openUnitIntervalRealAxisZetaZeroFree_of_etaValueFormula
      hetaValueFormula)

/--
The exponential-zeta Abel-boundary eta theorem discharges the project residual
axis target.
-/
theorem noResidualRealAxisZetaZeros_of_etaExpZetaBoundary
    (hexp : OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula) :
    NoResidualRealAxisZetaZeros :=
  noResidualRealAxisZetaZeros_of_openUnitIntervalRealAxisZetaZeroFree
    (openUnitIntervalRealAxisZetaZeroFree_of_etaExpZetaBoundary hexp)

/--
The reusable nonzero additive-character Abel theorem discharges the project
residual axis target through its `ZMod 2` eta specialization.
-/
theorem noResidualRealAxisZetaZeros_of_zmodAdditiveCharacter
    (hadd : ZModAdditiveCharacterAbelExpZetaBoundaryFormula) :
    NoResidualRealAxisZetaZeros :=
  noResidualRealAxisZetaZeros_of_etaExpZetaBoundary
    (openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodAdditiveCharacter
      hadd)

/--
The checked-boundary-value additive-character theorem discharges the project
residual axis target through the `ZMod 2` eta specialization.
-/
theorem noResidualRealAxisZetaZeros_of_zmodBoundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    NoResidualRealAxisZetaZeros :=
  noResidualRealAxisZetaZeros_of_openUnitIntervalRealAxisZetaZeroFree
    (openUnitIntervalRealAxisZetaZeroFree_of_zmodBoundaryValue hvalue)

/--
The isolated regularized Hurwitz-tail theorem discharges the project residual
real-axis target.
-/
theorem noResidualRealAxisZetaZeros_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    NoResidualRealAxisZetaZeros :=
  noResidualRealAxisZetaZeros_of_zmodBoundaryValue
    (zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitz
      htail)

/--
The source-shaped `ZMod 2` checked-boundary-value theorem discharges the
project residual axis target.
-/
theorem noResidualRealAxisZetaZeros_of_zmodTwoBoundaryValue
    (hvalue : ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula) :
    NoResidualRealAxisZetaZeros :=
  noResidualRealAxisZetaZeros_of_etaValueFormula
    (openUnitIntervalRiemannZetaEtaValueFormula_of_zmodTwoBoundaryValue hvalue)

/--
The project residual axis target is equivalent to the classical real-axis
zero classification.
-/
theorem realAxisZetaZeroClassification_of_noResidualRealAxisZetaZeros
    (hnoResidual : NoResidualRealAxisZetaZeros) :
    RealAxisZetaZeroClassification := by
  intro s hs haxis
  let rho : ZetaZeroSubtype :=
    ⟨s, by
      unfold IsZetaZero at hs
      exact mem_riemannZetaZeros.mpr hs⟩
  simpa [rho, IsKnownTrivialAxisZetaZero] using
    hnoResidual rho (by simpa [rho] using haxis)

/-- The residual axis target is exactly real-axis zeta-zero classification. -/
theorem noResidualRealAxisZetaZeros_iff_realAxisZetaZeroClassification :
    NoResidualRealAxisZetaZeros ↔ RealAxisZetaZeroClassification := by
  constructor
  · exact realAxisZetaZeroClassification_of_noResidualRealAxisZetaZeros
  · exact noResidualRealAxisZetaZeros_of_realAxisZetaZeroClassification

/--
The residual axis target is also equivalent to the left-half-plane
classification, since the right closed half-plane has no zeta zeroes.
-/
theorem noResidualRealAxisZetaZeros_iff_leftRealAxisZetaZeroClassification :
    NoResidualRealAxisZetaZeros ↔ LeftRealAxisZetaZeroClassification := by
  constructor
  · intro hno
    exact
      leftRealAxisZetaZeroClassification_of_realAxisZetaZeroClassification
        (realAxisZetaZeroClassification_of_noResidualRealAxisZetaZeros hno)
  · exact noResidualRealAxisZetaZeros_of_leftRealAxisZetaZeroClassification

/-- A no-residual-real-axis theorem empties every residual axis window. -/
theorem closedBallZeroResidualRealAxisFinset_eq_empty_of_noResidual
    (hnoResidual : NoResidualRealAxisZetaZeros) (n : Nat) :
    closedBallZeroResidualRealAxisFinset n = ∅ := by
  classical
  ext rho
  constructor
  · intro hrho
    have hmem := (mem_closedBallZeroResidualRealAxisFinset n).mp hrho
    have haxis := (mem_closedBallZeroAxisOrdinateFinset n).mp hmem.1
    exact (hmem.2 (hnoResidual rho haxis.2)).elim
  · intro hrho
    simp at hrho

/-- A no-residual-real-axis theorem makes every residual axis count zero. -/
theorem closedBallZeroResidualRealAxis_card_eq_zero_of_noResidual
    (hnoResidual : NoResidualRealAxisZetaZeros) (n : Nat) :
    (closedBallZeroResidualRealAxisFinset n).card = 0 := by
  rw [closedBallZeroResidualRealAxisFinset_eq_empty_of_noResidual
    hnoResidual n]
  simp

/--
A no-residual-real-axis theorem gives the residual axis window the zero linear
bound.
-/
theorem closedBallZeroResidualRealAxis_card_le_zero_linear_of_noResidual
    (hnoResidual : NoResidualRealAxisZetaZeros) (n : Nat) :
    ((closedBallZeroResidualRealAxisFinset n).card : Real) <=
      0 * ((n : Real) + 1) := by
  rw [closedBallZeroResidualRealAxis_card_eq_zero_of_noResidual hnoResidual n]
  norm_num

/--
With no residual real-axis zeroes, the full axis count is controlled by the
checked known-trivial linear bound alone.
-/
theorem closedBallZeroAxis_card_le_noResidualLinearAxisBound
    (hnoResidual : NoResidualRealAxisZetaZeros) (n : Nat) :
    ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
      1 * ((n : Real) + 1) := by
  simpa using
    (closedBallZeroAxis_card_le_splitLinearAxisBound
      closedBallZeroKnownTrivialAxis_card_le_linear
      (closedBallZeroResidualRealAxis_card_le_zero_linear_of_noResidual
        hnoResidual)
      n)

/--
The isolated regularized Hurwitz-tail theorem gives the classical real-axis
zeta-zero classification directly.
-/
theorem realAxisZetaZeroClassification_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    RealAxisZetaZeroClassification :=
  realAxisZetaZeroClassification_of_noResidualRealAxisZetaZeros
    (noResidualRealAxisZetaZeros_of_regularizedTailHurwitz htail)

/--
The isolated regularized Hurwitz-tail theorem gives the left-half-plane
real-axis zeta-zero classification directly.
-/
theorem leftRealAxisZetaZeroClassification_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    LeftRealAxisZetaZeroClassification :=
  leftRealAxisZetaZeroClassification_of_realAxisZetaZeroClassification
    (realAxisZetaZeroClassification_of_regularizedTailHurwitz htail)

/--
The isolated regularized Hurwitz-tail theorem empties every residual real-axis
window.
-/
theorem closedBallZeroResidualRealAxisFinset_eq_empty_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula)
    (n : Nat) :
    closedBallZeroResidualRealAxisFinset n = ∅ :=
  closedBallZeroResidualRealAxisFinset_eq_empty_of_noResidual
    (noResidualRealAxisZetaZeros_of_regularizedTailHurwitz htail) n

/--
The isolated regularized Hurwitz-tail theorem makes every residual real-axis
window count vanish.
-/
theorem closedBallZeroResidualRealAxis_card_eq_zero_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula)
    (n : Nat) :
    (closedBallZeroResidualRealAxisFinset n).card = 0 :=
  closedBallZeroResidualRealAxis_card_eq_zero_of_noResidual
    (noResidualRealAxisZetaZeros_of_regularizedTailHurwitz htail) n

/--
The isolated regularized Hurwitz-tail theorem gives the residual real-axis
window the zero linear bound.
-/
theorem closedBallZeroResidualRealAxis_card_le_zero_linear_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula)
    (n : Nat) :
    ((closedBallZeroResidualRealAxisFinset n).card : Real) <=
      0 * ((n : Real) + 1) :=
  closedBallZeroResidualRealAxis_card_le_zero_linear_of_noResidual
    (noResidualRealAxisZetaZeros_of_regularizedTailHurwitz htail) n

/--
The isolated regularized Hurwitz-tail theorem reduces the full real-axis zero
count to the checked known-trivial linear bound.
-/
theorem closedBallZeroAxis_card_le_noResidualLinearAxisBound_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula)
    (n : Nat) :
    ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
      1 * ((n : Real) + 1) :=
  closedBallZeroAxis_card_le_noResidualLinearAxisBound
    (noResidualRealAxisZetaZeros_of_regularizedTailHurwitz htail) n
end

end ComplexCompactExhaustion

end RiemannHypothesisProject
