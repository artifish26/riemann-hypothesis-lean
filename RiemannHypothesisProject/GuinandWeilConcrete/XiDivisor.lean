import Mathlib.Analysis.Complex.Convex
import RiemannHypothesisProject.GuinandWeilConcrete.WeightedRectangleArgumentPrinciple
import RiemannHypothesisProject.GuinandWeilConcrete.XiContourWeight
import RiemannHypothesisProject.RiemannVonMangoldt.RiemannXiMultiplicity

/-!
# Xi divisor normalization for the Guinand-Weil rectangle

This module supplies the divisor facts needed before applying a weighted
argument principle to `riemannXi`.  It proves that both fixed vertical walls
of the selected rectangle are zero-free and extends the existing local
xi-to-zeta multiplicity bridge from positive ordinates to every nontrivial
zeta zero.

These are normalization and contour-boundary bridge theorems.  No weighted
rectangle identity is assumed here.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open Complex Filter Topology
open scoped Topology

/-- Xi has no zero in the open half-plane `1 < re s`. -/
theorem riemannXi_ne_zero_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro hone
    rw [hone] at hs
    norm_num at hs
  rw [riemannXi_eq_completedRiemannZeta hs0 hs1]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
    · intro hcompleted
      apply riemannZeta_ne_zero_of_one_lt_re hs
      rw [riemannZeta_def_of_ne_zero hs0, hcompleted, zero_div]
  · norm_num

/-- Xi has no zero in the reflected open half-plane `re s < 0`. -/
theorem riemannXi_ne_zero_of_re_neg
    {s : Complex} (hs : s.re < 0) :
    riemannXi s ≠ 0 := by
  have hreflected : 1 < (1 - s).re := by
    simp
    linarith
  simpa only [riemannXi_one_sub] using
    riemannXi_ne_zero_of_one_lt_re hreflected

/-- Xi has no zero on the fixed right wall `re s = 5/4`. -/
theorem riemannXi_ne_zero_of_re_eq_guinandWeilXiContourRight
    {s : Complex} (hs : s.re = guinandWeilXiContourRight) :
    riemannXi s ≠ 0 := by
  have hre : 1 < s.re := by
    rw [hs]
    norm_num [guinandWeilXiContourRight]
  exact riemannXi_ne_zero_of_one_lt_re hre

/-- Xi has no zero on the reflected fixed left wall `re s = -1/4`. -/
theorem riemannXi_ne_zero_of_re_eq_guinandWeilXiContourLeft
    {s : Complex} (hs : s.re = guinandWeilXiContourLeft) :
    riemannXi s ≠ 0 := by
  have hreflected : (1 - s).re = guinandWeilXiContourRight := by
    norm_num [hs, guinandWeilXiContourLeft, guinandWeilXiContourRight]
  simpa only [riemannXi_one_sub] using
    riemannXi_ne_zero_of_re_eq_guinandWeilXiContourRight hreflected

/-- Every nontrivial zeta zero has strictly positive real part.  This is the
all-ordinate form needed to keep the xi-to-zeta Gamma factor nonvanishing. -/
theorem zetaZeroSubtype_re_pos_of_not_trivial
    (rho : ZetaZeroSubtype)
    (hnotTrivial : Not (IsTrivialZetaZero (rho : Complex))) :
    0 < (rho : Complex).re := by
  have hre_nonneg : 0 <= (rho : Complex).re :=
    zetaZeroSubtype_re_nonneg_of_not_trivial rho hnotTrivial
  by_contra hnotPos
  have hre_zero : (rho : Complex).re = 0 :=
    le_antisymm (le_of_not_gt hnotPos) hre_nonneg
  have hrho0 : (rho : Complex) ≠ 0 := by
    intro hzero
    have hz : IsZetaZero (rho : Complex) := rho.property
    rw [hzero] at hz
    norm_num [IsZetaZero, riemannZeta_zero] at hz
  have hgamma : Complex.Gammaℝ (rho : Complex) ≠ 0 := by
    intro hzero
    rcases Complex.Gammaℝ_eq_zero_iff.mp hzero with ⟨n, hn⟩
    cases n with
    | zero =>
        apply hrho0
        simpa using hn
    | succ n =>
        apply hnotTrivial
        refine ⟨n, ?_⟩
        simpa [Nat.cast_succ] using hn
  have hrho1 : (rho : Complex) ≠ 1 := by
    intro hone
    have hre := (show IsZetaZero (rho : Complex) from rho.property).re_lt_one
    rw [hone] at hre
    norm_num at hre
  have hone_sub_ne_zero : (1 - (rho : Complex)) ≠ 0 := by
    exact sub_ne_zero.mpr hrho1.symm
  have hcompleted_zero : completedRiemannZeta (rho : Complex) = 0 := by
    have hzeta : riemannZeta (rho : Complex) = 0 := rho.property
    rw [riemannZeta_def_of_ne_zero hrho0] at hzeta
    exact (div_eq_zero_iff.mp hzeta).resolve_right hgamma
  have hmirror_zero : completedRiemannZeta (1 - (rho : Complex)) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact hcompleted_zero
  have hmirror_zeta_zero : riemannZeta (1 - (rho : Complex)) = 0 := by
    rw [riemannZeta_def_of_ne_zero hone_sub_ne_zero, hmirror_zero, zero_div]
  have hmirror_re : 1 <= (1 - (rho : Complex)).re := by
    simp [hre_zero]
  exact (riemannZeta_ne_zero_of_one_le_re hmirror_re) hmirror_zeta_zero

/-- The xi-to-zeta factor is analytic at every nontrivial zeta zero. -/
theorem analyticAt_xiToZetaFactor_of_not_trivial
    (rho : ZetaZeroSubtype)
    (_hnotTrivial : Not (IsTrivialZetaZero (rho : Complex))) :
    AnalyticAt Complex xiToZetaFactor (rho : Complex) := by
  have hrho0 : (rho : Complex) ≠ 0 := by
    intro hzero
    have hz : IsZetaZero (rho : Complex) := rho.property
    rw [hzero] at hz
    norm_num [IsZetaZero, riemannZeta_zero] at hz
  have hrho1 : (rho : Complex) ≠ 1 := by
    intro hone
    have hre := (show IsZetaZero (rho : Complex) from rho.property).re_lt_one
    rw [hone] at hre
    norm_num at hre
  have hpoly :
      AnalyticAt Complex (fun s : Complex => s * (s - 1)) (rho : Complex) := by
    fun_prop
  have hpoly_ne : (rho : Complex) * ((rho : Complex) - 1) ≠ 0 :=
    mul_ne_zero hrho0 (sub_ne_zero.mpr hrho1)
  have hgamma :
      AnalyticAt Complex (fun s : Complex => (Complex.Gammaℝ s)⁻¹)
        (rho : Complex) :=
    Complex.differentiable_Gammaℝ_inv.analyticAt _
  unfold xiToZetaFactor
  exact ((analyticAt_const.mul hgamma).mul (hpoly.inv hpoly_ne))

/-- The xi-to-zeta factor is nonzero at every nontrivial zeta zero. -/
theorem xiToZetaFactor_ne_zero_of_not_trivial
    (rho : ZetaZeroSubtype)
    (hnotTrivial : Not (IsTrivialZetaZero (rho : Complex))) :
    xiToZetaFactor (rho : Complex) ≠ 0 := by
  have hre : 0 < (rho : Complex).re :=
    zetaZeroSubtype_re_pos_of_not_trivial rho hnotTrivial
  have hrho0 : (rho : Complex) ≠ 0 := by
    intro hzero
    rw [hzero] at hre
    norm_num at hre
  have hrho1 : (rho : Complex) ≠ 1 := by
    intro hone
    have hlt := (show IsZetaZero (rho : Complex) from rho.property).re_lt_one
    rw [hone] at hlt
    norm_num at hlt
  unfold xiToZetaFactor
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hre)))
    (inv_ne_zero (mul_ne_zero hrho0 (sub_ne_zero.mpr hrho1)))

/-- Near every nontrivial zeta zero, zeta is the product of the nonvanishing
xi-to-zeta factor and xi. -/
theorem riemannZeta_eventuallyEq_xiToZetaFactor_mul_riemannXi_of_not_trivial
    (rho : ZetaZeroSubtype)
    (hnotTrivial : Not (IsTrivialZetaZero (rho : Complex))) :
    riemannZeta =ᶠ[𝓝 (rho : Complex)]
      fun s => xiToZetaFactor s * riemannXi s := by
  have hrho0 : (rho : Complex) ≠ 0 := by
    intro hzero
    have hz : IsZetaZero (rho : Complex) := rho.property
    rw [hzero] at hz
    norm_num [IsZetaZero, riemannZeta_zero] at hz
  have hrho1 : (rho : Complex) ≠ 1 := by
    intro hone
    have hre := (show IsZetaZero (rho : Complex) from rho.property).re_lt_one
    rw [hone] at hre
    norm_num at hre
  have hrhore : 0 < (rho : Complex).re :=
    zetaZeroSubtype_re_pos_of_not_trivial rho hnotTrivial
  have hright : ∀ᶠ s : Complex in 𝓝 (rho : Complex), 0 < s.re :=
    (Complex.continuous_re.tendsto (rho : Complex)).eventually (lt_mem_nhds hrhore)
  filter_upwards [eventually_ne_nhds hrho0, eventually_ne_nhds hrho1, hright]
    with s hs0 hs1 hsre
  rw [riemannXi_eq_completedRiemannZeta hs0 hs1]
  rw [riemannZeta_def_of_ne_zero hs0]
  unfold xiToZetaFactor
  rw [div_eq_mul_inv]
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp [hs0, hs1, hsub, Complex.Gammaℝ_ne_zero_of_re_pos hsre]

/-- Xi's analytic divisor order is the project's zeta-zero multiplicity at
every nontrivial zeta zero, without an ordinate-sign restriction. -/
theorem analyticOrderAt_riemannXi_eq_zetaZeroMultiplicity_of_not_trivial
    (rho : ZetaZeroSubtype)
    (hnotTrivial : Not (IsTrivialZetaZero (rho : Complex))) :
    analyticOrderAt riemannXi (rho : Complex) =
      zetaZeroMultiplicity rho := by
  have hfactor := analyticAt_xiToZetaFactor_of_not_trivial rho hnotTrivial
  have hxi : AnalyticAt Complex riemannXi (rho : Complex) :=
    differentiable_riemannXi.analyticAt _
  have hfactor_order :
      analyticOrderAt xiToZetaFactor (rho : Complex) = 0 :=
    hfactor.analyticOrderAt_eq_zero.mpr
      (xiToZetaFactor_ne_zero_of_not_trivial rho hnotTrivial)
  have hcongr :
      analyticOrderAt riemannZeta (rho : Complex) =
        analyticOrderAt (xiToZetaFactor * riemannXi) (rho : Complex) := by
    exact analyticOrderAt_congr
      (riemannZeta_eventuallyEq_xiToZetaFactor_mul_riemannXi_of_not_trivial
        rho hnotTrivial)
  rw [analyticOrderAt_mul hfactor hxi, hfactor_order, zero_add] at hcongr
  rw [← hcongr, analyticOrderAt_riemannZeta_eq_zetaZeroMultiplicity]

/-- Meromorphic-order form of the all-ordinate xi/zeta multiplicity bridge. -/
theorem meromorphicOrderAt_riemannXi_eq_zetaZeroMultiplicity_of_not_trivial
    (rho : ZetaZeroSubtype)
    (hnotTrivial : Not (IsTrivialZetaZero (rho : Complex))) :
    meromorphicOrderAt riemannXi (rho : Complex) =
      ((zetaZeroMultiplicity rho : Int) : WithTop Int) := by
  rw [(differentiable_riemannXi.analyticAt (rho : Complex)).meromorphicOrderAt_eq,
    analyticOrderAt_riemannXi_eq_zetaZeroMultiplicity_of_not_trivial
      rho hnotTrivial]
  simp

/-- Local weighted xi argument principle at an arbitrary nontrivial zero.  The
residue coefficient is the complete analytic multiplicity. -/
theorem guinandWeilSimpleResidue_xiContourWeight_mul_logDeriv_riemannXi
    (p : Polynomial Real) (rho : ZetaZeroSubtype)
    (hnotTrivial : Not (IsTrivialZetaZero (rho : Complex))) :
    guinandWeilSimpleResidue
        (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
        (rho : Complex) =
      guinandWeilXiContourWeight p (rho : Complex) *
        (zetaZeroMultiplicity rho : Complex) := by
  simpa using
    (guinandWeilSimpleResidue_weight_mul_logDeriv_eq
      (H := guinandWeilXiContourWeight p)
      (f := riemannXi)
      (n := (zetaZeroMultiplicity rho : Int))
      (differentiable_guinandWeilXiContourWeight p |>.analyticAt (rho : Complex))
      (differentiable_riemannXi.analyticAt (rho : Complex) |>.meromorphicAt)
      (meromorphicOrderAt_riemannXi_eq_zetaZeroMultiplicity_of_not_trivial
        rho hnotTrivial))

/-- A zero of xi is an actual zeta zero. -/
theorem isZetaZero_of_riemannXi_eq_zero
    {s : Complex} (hxi : riemannXi s = 0) :
    IsZetaZero s := by
  have hs0 : s ≠ 0 := by
    intro hzero
    subst s
    norm_num [riemannXi] at hxi
  have hs1 : s ≠ 1 := by
    intro hone
    subst s
    norm_num [riemannXi] at hxi
  have hcompleted : completedRiemannZeta s = 0 := by
    rw [riemannXi_eq_completedRiemannZeta hs0 hs1] at hxi
    rcases div_eq_zero_iff.mp hxi with hproduct | htwo
    · rcases mul_eq_zero.mp hproduct with hpoly | hcompleted
      · exact False.elim ((mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hpoly)
      · exact hcompleted
    · norm_num at htwo
  unfold IsZetaZero
  rw [riemannZeta_def_of_ne_zero hs0, hcompleted, zero_div]

/-- A zero of xi cannot be a trivial zeta zero. -/
theorem not_isTrivialZetaZero_of_riemannXi_eq_zero
    {s : Complex} (hxi : riemannXi s = 0) :
    Not (IsTrivialZetaZero s) := by
  intro htrivial
  rcases htrivial with ⟨n, rfl⟩
  apply riemannXi_ne_zero_of_re_neg (s := -2 * ((n : Complex) + 1))
  · norm_num
    positivity
  · exact hxi

/-- A zero of xi, packaged as an element of the project's zeta-zero subtype. -/
noncomputable def zetaZeroSubtypeOfRiemannXiZero
    (s : Complex) (hxi : riemannXi s = 0) : ZetaZeroSubtype :=
  ⟨s, by
    simpa [IsZetaZero, riemannZetaZeros] using
      isZetaZero_of_riemannXi_eq_zero hxi⟩

/-- Xi's divisor has finite support on every closed rectangle. -/
theorem riemannXiRectangleDivisorSupport_finite (z w : Complex) :
    (MeromorphicOn.divisor riemannXi (Rectangle z w)).support.Finite := by
  exact (MeromorphicOn.divisor riemannXi (Rectangle z w)).finiteSupport
    (IsCompact.reProdIm isCompact_uIcc isCompact_uIcc)

/-- The finite support of xi's divisor on a closed rectangle. -/
noncomputable def riemannXiRectangleDivisorSupport
    (z w : Complex) : Finset Complex :=
  (riemannXiRectangleDivisorSupport_finite z w).toFinset

/-- Xi has finite analytic order at every point.  This rules out the
identically-zero branch of the local analytic-order API. -/
theorem analyticOrderAt_riemannXi_ne_top (s : Complex) :
    analyticOrderAt riemannXi s ≠ ⊤ := by
  apply (analyticOnNhd_riemannXi Set.univ).analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (x := (2 : Complex)) (y := s) trivial trivial
  rw [(differentiable_riemannXi.analyticAt 2).analyticOrderAt_eq_zero.mpr
    riemannXi_two_ne_zero]
  simp

@[simp]
theorem mem_riemannXiRectangleDivisorSupport
    {z w s : Complex} :
    s ∈ riemannXiRectangleDivisorSupport z w ↔
      s ∈ (MeromorphicOn.divisor riemannXi (Rectangle z w)).support := by
  simp [riemannXiRectangleDivisorSupport]

/-- Every point in the finite rectangle divisor support is a zero of xi. -/
theorem riemannXi_eq_zero_of_mem_rectangleDivisorSupport
    {z w s : Complex}
    (hs : s ∈ riemannXiRectangleDivisorSupport z w) :
    riemannXi s = 0 := by
  have hsSupport :
      s ∈ (MeromorphicOn.divisor riemannXi (Rectangle z w)).support :=
    mem_riemannXiRectangleDivisorSupport.mp hs
  have hsRectangle : s ∈ Rectangle z w :=
    (MeromorphicOn.divisor riemannXi (Rectangle z w)).supportWithinDomain hsSupport
  have hdivisor_ne :
      MeromorphicOn.divisor riemannXi (Rectangle z w) s ≠ 0 := by
    simpa [Function.mem_support] using hsSupport
  have horder_ne : analyticOrderAt riemannXi s ≠ 0 := by
    intro horder
    apply hdivisor_ne
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
      (analyticOnNhd_riemannXi (Rectangle z w)) hsRectangle, horder]
    simp
  exact apply_eq_zero_of_analyticOrderAt_ne_zero horder_ne

/-- Xi's rectangle divisor support is exactly its zero set inside that
rectangle.  In particular, no interior xi zero can be omitted from the
finite residue sum. -/
theorem mem_riemannXiRectangleDivisorSupport_iff
    {z w s : Complex} :
    s ∈ riemannXiRectangleDivisorSupport z w ↔
      s ∈ Rectangle z w ∧ riemannXi s = 0 := by
  constructor
  · intro hs
    exact ⟨
      (MeromorphicOn.divisor riemannXi (Rectangle z w)).supportWithinDomain
        (mem_riemannXiRectangleDivisorSupport.mp hs),
      riemannXi_eq_zero_of_mem_rectangleDivisorSupport hs⟩
  · rintro ⟨hsR, hxi⟩
    rw [mem_riemannXiRectangleDivisorSupport, Function.mem_support]
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
      (analyticOnNhd_riemannXi (Rectangle z w)) hsR]
    have horder_ne_zero : analyticOrderAt riemannXi s ≠ 0 :=
      (differentiable_riemannXi.analyticAt s).analyticOrderAt_ne_zero.mpr hxi
    have horder_ne_top : analyticOrderAt riemannXi s ≠ ⊤ :=
      analyticOrderAt_riemannXi_ne_top s
    rw [← ENat.coe_toNat horder_ne_top] at horder_ne_zero ⊢
    simpa using horder_ne_zero

/-- The zeta zero represented by one point of xi's rectangle divisor support. -/
noncomputable def riemannXiRectangleZetaZero
    (z w : Complex) (s : Complex)
    (hs : s ∈ riemannXiRectangleDivisorSupport z w) : ZetaZeroSubtype :=
  zetaZeroSubtypeOfRiemannXiZero s
    (riemannXi_eq_zero_of_mem_rectangleDivisorSupport hs)

/-- Every rectangle divisor point is nontrivial. -/
theorem not_isTrivialZetaZero_riemannXiRectangleZetaZero
    (z w : Complex) (s : Complex)
    (hs : s ∈ riemannXiRectangleDivisorSupport z w) :
    Not (IsTrivialZetaZero
      (riemannXiRectangleZetaZero z w s hs : Complex)) := by
  exact not_isTrivialZetaZero_of_riemannXi_eq_zero
    (riemannXi_eq_zero_of_mem_rectangleDivisorSupport hs)

/-- Weighted logarithmic-derivative residue at one point selected by xi's
rectangle divisor support. -/
theorem guinandWeilSimpleResidue_xiContourWeight_mul_logDeriv_riemannXi_of_mem_rectangleDivisorSupport
    (p : Polynomial Real) (z w : Complex) (s : Complex)
    (hs : s ∈ riemannXiRectangleDivisorSupport z w) :
    guinandWeilSimpleResidue
        (fun u => guinandWeilXiContourWeight p u * logDeriv riemannXi u) s =
      guinandWeilXiContourWeight p s *
        (zetaZeroMultiplicity (riemannXiRectangleZetaZero z w s hs) : Complex) := by
  let rho : ZetaZeroSubtype := riemannXiRectangleZetaZero z w s hs
  have hrho : (rho : Complex) = s := rfl
  change guinandWeilSimpleResidue
      (fun u => guinandWeilXiContourWeight p u * logDeriv riemannXi u) s =
    guinandWeilXiContourWeight p s * (zetaZeroMultiplicity rho : Complex)
  rw [← hrho]
  exact guinandWeilSimpleResidue_xiContourWeight_mul_logDeriv_riemannXi
    p rho (by
      simpa [rho] using
        not_isTrivialZetaZero_riemannXiRectangleZetaZero z w s hs)

/-- The natural analytic order attached to each rectangle divisor point is
the project's zeta-zero multiplicity. -/
theorem analyticOrderNatAt_riemannXi_eq_zetaZeroMultiplicity_of_mem_rectangleDivisorSupport
    (z w : Complex) (s : Complex)
    (hs : s ∈ riemannXiRectangleDivisorSupport z w) :
    analyticOrderNatAt riemannXi s =
      zetaZeroMultiplicity (riemannXiRectangleZetaZero z w s hs) := by
  have horder :=
    analyticOrderAt_riemannXi_eq_zetaZeroMultiplicity_of_not_trivial
      (riemannXiRectangleZetaZero z w s hs)
      (not_isTrivialZetaZero_riemannXiRectangleZetaZero z w s hs)
  change analyticOrderNatAt riemannXi
    (riemannXiRectangleZetaZero z w s hs : Complex) = _
  unfold analyticOrderNatAt
  rw [horder]
  simp

/-- The finite weighted xi-zero sum on a rectangle, indexed by the actual
divisor support rather than an unrelated compact exhaustion. -/
noncomputable def riemannXiRectangleWeightedZeroSum
    (H : Complex → Complex) (z w : Complex) : Complex :=
  ∑ s ∈ (riemannXiRectangleDivisorSupport z w).attach,
    (analyticOrderNatAt riemannXi (s : Complex) : Complex) * H s

/-- Multiplicity-correct expansion of the finite weighted rectangle zero sum. -/
theorem riemannXiRectangleWeightedZeroSum_eq_zetaZeroMultiplicity
    (H : Complex → Complex) (z w : Complex) :
    riemannXiRectangleWeightedZeroSum H z w =
      ∑ s ∈ (riemannXiRectangleDivisorSupport z w).attach,
        (zetaZeroMultiplicity
          (riemannXiRectangleZetaZero z w s s.property) : Complex) * H s := by
  classical
  unfold riemannXiRectangleWeightedZeroSum
  apply Finset.sum_congr rfl
  intro s hs
  rw [analyticOrderNatAt_riemannXi_eq_zetaZeroMultiplicity_of_mem_rectangleDivisorSupport
    z w s s.property]

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
