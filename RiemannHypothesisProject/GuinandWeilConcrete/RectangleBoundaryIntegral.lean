import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-
The oriented rectangle definitions and the direct Cauchy-kernel calculation
are adapted from PrimeNumberTheoremAnd, `ResidueCalcOnRectangles.lean`, under
the Apache 2.0 license.  This is a project-local, reduced port for the current
Mathlib API.

https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
-/

/-!
# Oriented rectangle boundary integrals

This module provides the zeta-independent contour source used by the weighted
argument principle.  It defines the four oriented side integrals, proves
Cauchy-Goursat vanishing for an analytic remainder, evaluates the simple
Cauchy kernel on an arbitrary rectangle, and sums finitely many principal
parts.
-/

namespace RiemannHypothesisProject

noncomputable section

open Complex MeasureTheory Set Topology intervalIntegral
open scoped Interval Topology

/-- Integral along a horizontal segment, oriented from `x₁` to `x₂`. -/
noncomputable def guinandWeilHorizontalIntegral
    (F : Complex → Complex) (x₁ x₂ y : Real) : Complex :=
  ∫ x in x₁..x₂, F (x + y * Complex.I)

/-- Integral along a vertical segment, oriented from `y₁` to `y₂`. -/
noncomputable def guinandWeilVerticalIntegral
    (F : Complex → Complex) (x y₁ y₂ : Real) : Complex :=
  Complex.I * ∫ y in y₁..y₂, F (x + y * Complex.I)

/-- Positively oriented integral around the rectangle with opposite corners
`z` and `w`. -/
noncomputable def guinandWeilRectangleIntegral
    (F : Complex → Complex) (z w : Complex) : Complex :=
  guinandWeilHorizontalIntegral F z.re w.re z.im -
      guinandWeilHorizontalIntegral F z.re w.re w.im +
    guinandWeilVerticalIntegral F w.re z.im w.im -
      guinandWeilVerticalIntegral F z.re z.im w.im

/-- Rectangle boundary integral normalized by `2 * π * I`. -/
noncomputable def guinandWeilNormalizedRectangleIntegral
    (F : Complex → Complex) (z w : Complex) : Complex :=
  (1 / (2 * Real.pi * Complex.I)) * guinandWeilRectangleIntegral F z w

/-- The union of the four sides of a complex rectangle. -/
def guinandWeilRectangleBorder (z w : Complex) : Set Complex :=
  Set.uIcc z.re w.re ×ℂ {z.im} ∪
    {z.re} ×ℂ Set.uIcc z.im w.im ∪
    Set.uIcc z.re w.re ×ℂ {w.im} ∪
    {w.re} ×ℂ Set.uIcc z.im w.im

theorem guinandWeilRectangleBorder_subset_rectangle (z w : Complex) :
    guinandWeilRectangleBorder z w ⊆ Complex.Rectangle z w := by
  intro s hs
  rcases hs with ((hs | hs) | hs) | hs
  · exact ⟨hs.1, hs.2 ▸ Set.left_mem_uIcc⟩
  · exact ⟨hs.1 ▸ Set.left_mem_uIcc, hs.2⟩
  · exact ⟨hs.1, hs.2 ▸ Set.right_mem_uIcc⟩
  · exact ⟨hs.1 ▸ Set.right_mem_uIcc, hs.2⟩

theorem guinandWeilRectangle_mem_nhds_iff
    {z w p : Complex} :
    Complex.Rectangle z w ∈ 𝓝 p ↔
      p ∈ Set.uIoo z.re w.re ×ℂ Set.uIoo z.im w.im := by
  simp_rw [← mem_interior_iff_mem_nhds, Complex.Rectangle,
    Complex.interior_reProdIm, Set.uIoo, Set.uIcc, interior_Icc]

theorem not_mem_guinandWeilRectangleBorder_of_rectangle_mem_nhds
    {z w p : Complex}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hp : Complex.Rectangle z w ∈ 𝓝 p) :
    p ∉ guinandWeilRectangleBorder z w := by
  rw [guinandWeilRectangle_mem_nhds_iff,
    Set.uIoo_of_le hzre, Set.uIoo_of_le hzim] at hp
  rintro (((hbottom | hleft) | htop) | hright)
  · exact hp.2.1.ne (by simpa using hbottom.2.symm)
  · exact hp.1.1.ne (by simpa using hleft.1.symm)
  · exact hp.2.2.ne' (by simpa using htop.2.symm)
  · exact hp.1.2.ne' (by simpa using hright.1.symm)

/-- A point of an ordered rectangle that is on none of its four sides lies
in the rectangle interior. -/
theorem guinandWeilRectangle_mem_nhds_of_mem_not_border
    {z w p : Complex}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hpR : p ∈ Complex.Rectangle z w)
    (hpnot : p ∉ guinandWeilRectangleBorder z w) :
    Complex.Rectangle z w ∈ nhds p := by
  rw [Complex.Rectangle, Set.uIcc_of_le hzre, Set.uIcc_of_le hzim,
    Complex.mem_reProdIm, Set.mem_Icc, Set.mem_Icc] at hpR
  have hp_re_left : z.re < p.re :=
    lt_of_le_of_ne hpR.1.1 fun hEq => hpnot
      (Or.inl (Or.inl (Or.inr (by
        rw [Complex.mem_reProdIm, Set.mem_singleton_iff]
        exact ⟨hEq.symm, by simpa [Set.uIcc_of_le hzim] using hpR.2⟩))))
  have hp_re_right : p.re < w.re :=
    lt_of_le_of_ne hpR.1.2 fun hEq => hpnot
      (Or.inr (by
        rw [Complex.mem_reProdIm, Set.mem_singleton_iff]
        exact ⟨hEq, by simpa [Set.uIcc_of_le hzim] using hpR.2⟩))
  have hp_im_bottom : z.im < p.im :=
    lt_of_le_of_ne hpR.2.1 fun hEq => hpnot
      (Or.inl (Or.inl (Or.inl (by
        rw [Complex.mem_reProdIm, Set.mem_singleton_iff]
        exact ⟨by simpa [Set.uIcc_of_le hzre] using hpR.1, hEq.symm⟩))))
  have hp_im_top : p.im < w.im :=
    lt_of_le_of_ne hpR.2.2 fun hEq => hpnot
      (Or.inl (Or.inr (by
        rw [Complex.mem_reProdIm, Set.mem_singleton_iff]
        exact ⟨by simpa [Set.uIcc_of_le hzre] using hpR.1, hEq⟩)))
  rw [guinandWeilRectangle_mem_nhds_iff,
    Set.uIoo_of_le hzre, Set.uIoo_of_le hzim]
  exact ⟨⟨hp_re_left, hp_re_right⟩, ⟨hp_im_bottom, hp_im_top⟩⟩

/-- Integrability of all four parameterized rectangle sides. -/
def GuinandWeilRectangleBorderIntegrable
    (F : Complex → Complex) (z w : Complex) : Prop :=
  IntervalIntegrable (fun x => F (x + z.im * Complex.I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => F (x + w.im * Complex.I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => F (w.re + y * Complex.I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => F (z.re + y * Complex.I)) volume z.im w.im

theorem continuousOn_rectangleBorder_integrable
    {F : Complex → Complex} {z w : Complex}
    (hF : ContinuousOn F (guinandWeilRectangleBorder z w)) :
    GuinandWeilRectangleBorderIntegrable F z w := by
  constructor
  · exact (hF.comp (by fun_prop) (by
      intro x hx
      exact Or.inl (Or.inl (Or.inl ⟨by simpa, by simp⟩)))).intervalIntegrable
  constructor
  · exact (hF.comp (by fun_prop) (by
      intro x hx
      exact Or.inl (Or.inr ⟨by simpa, by simp⟩))).intervalIntegrable
  constructor
  · exact (hF.comp (by fun_prop) (by
      intro y hy
      exact Or.inr ⟨by simp, by simpa⟩)).intervalIntegrable
  · exact (hF.comp (by fun_prop) (by
      intro y hy
      exact Or.inl (Or.inl (Or.inr ⟨by simp, by simpa⟩)))).intervalIntegrable

/-- Rectangle integration is additive when both boundary restrictions are
integrable. -/
theorem guinandWeilRectangleIntegral_add
    {F G : Complex → Complex} {z w : Complex}
    (hF : GuinandWeilRectangleBorderIntegrable F z w)
    (hG : GuinandWeilRectangleBorderIntegrable G z w) :
    guinandWeilRectangleIntegral (fun s => F s + G s) z w =
      guinandWeilRectangleIntegral F z w +
        guinandWeilRectangleIntegral G z w := by
  unfold guinandWeilRectangleIntegral guinandWeilHorizontalIntegral
    guinandWeilVerticalIntegral
  rw [intervalIntegral.integral_add hF.1 hG.1,
    intervalIntegral.integral_add hF.2.1 hG.2.1,
    intervalIntegral.integral_add hF.2.2.1 hG.2.2.1,
    intervalIntegral.integral_add hF.2.2.2 hG.2.2.2]
  ring

theorem guinandWeilNormalizedRectangleIntegral_add
    {F G : Complex → Complex} {z w : Complex}
    (hF : GuinandWeilRectangleBorderIntegrable F z w)
    (hG : GuinandWeilRectangleBorderIntegrable G z w) :
    guinandWeilNormalizedRectangleIntegral (fun s => F s + G s) z w =
      guinandWeilNormalizedRectangleIntegral F z w +
        guinandWeilNormalizedRectangleIntegral G z w := by
  unfold guinandWeilNormalizedRectangleIntegral
  rw [guinandWeilRectangleIntegral_add hF hG]
  ring

/-- Boundary integrals depend only on boundary values. -/
theorem guinandWeilRectangleIntegral_congr
    {F G : Complex → Complex} {z w : Complex}
    (h : Set.EqOn F G (guinandWeilRectangleBorder z w)) :
    guinandWeilRectangleIntegral F z w =
      guinandWeilRectangleIntegral G z w := by
  unfold guinandWeilRectangleIntegral guinandWeilHorizontalIntegral
    guinandWeilVerticalIntegral
  have hbottom :
      (∫ x in z.re..w.re, F (x + z.im * Complex.I)) =
        ∫ x in z.re..w.re, G (x + z.im * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact h (Or.inl (Or.inl (Or.inl ⟨by simpa, by simp⟩)))
  have htop :
      (∫ x in z.re..w.re, F (x + w.im * Complex.I)) =
        ∫ x in z.re..w.re, G (x + w.im * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact h (Or.inl (Or.inr ⟨by simpa, by simp⟩))
  have hright :
      (∫ y in z.im..w.im, F (w.re + y * Complex.I)) =
        ∫ y in z.im..w.im, G (w.re + y * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact h (Or.inr ⟨by simp, by simpa⟩)
  have hleft :
      (∫ y in z.im..w.im, F (z.re + y * Complex.I)) =
        ∫ y in z.im..w.im, G (z.re + y * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact h (Or.inl (Or.inl (Or.inr ⟨by simp, by simpa⟩)))
  rw [hbottom, htop, hright, hleft]

theorem guinandWeilNormalizedRectangleIntegral_congr
    {F G : Complex → Complex} {z w : Complex}
    (h : Set.EqOn F G (guinandWeilRectangleBorder z w)) :
    guinandWeilNormalizedRectangleIntegral F z w =
      guinandWeilNormalizedRectangleIntegral G z w := by
  unfold guinandWeilNormalizedRectangleIntegral
  rw [guinandWeilRectangleIntegral_congr h]

/-- Cauchy-Goursat vanishing in the local rectangle notation. -/
theorem guinandWeilRectangleIntegral_eq_zero_of_differentiableOn
    {F : Complex → Complex} {z w : Complex}
    (hF : DifferentiableOn Complex F (Complex.Rectangle z w)) :
    guinandWeilRectangleIntegral F z w = 0 := by
  unfold guinandWeilRectangleIntegral guinandWeilHorizontalIntegral
    guinandWeilVerticalIntegral
  simpa [smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hF

theorem guinandWeilNormalizedRectangleIntegral_eq_zero_of_differentiableOn
    {F : Complex → Complex} {z w : Complex}
    (hF : DifferentiableOn Complex F (Complex.Rectangle z w)) :
    guinandWeilNormalizedRectangleIntegral F z w = 0 := by
  unfold guinandWeilNormalizedRectangleIntegral
  rw [guinandWeilRectangleIntegral_eq_zero_of_differentiableOn hF, mul_zero]

theorem guinandWeilRectangleIntegral_translate
    (F : Complex → Complex) (z w p : Complex) :
    guinandWeilRectangleIntegral (fun s => F (s - p)) z w =
      guinandWeilRectangleIntegral F (z - p) (w - p) := by
  simp_rw [guinandWeilRectangleIntegral, guinandWeilHorizontalIntegral,
    guinandWeilVerticalIntegral, Complex.sub_re, Complex.sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

theorem guinandWeilNormalizedRectangleIntegral_translate
    (F : Complex → Complex) (z w p : Complex) :
    guinandWeilNormalizedRectangleIntegral (fun s => F (s - p)) z w =
      guinandWeilNormalizedRectangleIntegral F (z - p) (w - p) := by
  unfold guinandWeilNormalizedRectangleIntegral
  rw [guinandWeilRectangleIntegral_translate]

private theorem complex_inv_re_add_im {x y : Real} :
    ((x : Complex) + (y : Complex) * Complex.I)⁻¹ =
      ((x : Complex) - Complex.I * (y : Complex)) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [Complex.conj_ofReal, Complex.normSq] <;> ring

private theorem sq_add_sq_ne_zero {x y : Real} (hy : y ≠ 0) :
    x ^ 2 + y ^ 2 ≠ 0 := by
  nlinarith [sq_nonneg x, sq_pos_of_ne_zero hy]

private theorem continuous_self_div_sq_add_sq {y : Real} (hy : y ≠ 0) :
    Continuous fun x : Real => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const)
    (fun _ => sq_add_sq_ne_zero hy)

private theorem integral_self_div_sq_add_sq
    {x₁ x₂ y : Real} (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
      Real.log (x₂ ^ 2 + y ^ 2) / 2 -
        Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : Real) : Real := Real.log (x ^ 2 + y ^ 2) / 2
  have hderiv {x : Real} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    have hinner := HasDerivAt.add_const (y ^ 2) (by
      simpa using hasDerivAt_pow 2 x)
    convert! (hinner.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    field_simp
  have hderiv_eq : deriv f = fun x => x / (x ^ 2 + y ^ 2) :=
    funext fun _ => hderiv.deriv
  have hcontinuous : Continuous (deriv f) := by
    simpa only [hderiv_eq] using continuous_self_div_sq_add_sq hy
  simp_rw [← hderiv.deriv]
  exact integral_deriv_eq_sub (fun _ _ => hderiv.differentiableAt)
    (hcontinuous.intervalIntegrable _ _)

private theorem integral_const_div_sq_add_sq
    {x₁ x₂ y : Real} (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) =
      Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right,
    ← intervalIntegral.integral_const_mul, ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring

private theorem integral_const_div_self_add_im
    {A : Complex} {x₁ x₂ y : Real} (hy : y ≠ 0) :
    ∫ x : Real in x₁..x₂, A / ((x : Complex) + (y : Complex) * Complex.I) =
      A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 -
        Real.log (x₁ ^ 2 + y ^ 2) / 2) -
      A * Complex.I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have hsplit {x : Real} :
      A / ((x : Complex) + (y : Complex) * Complex.I) =
        A * x / (x ^ 2 + y ^ 2) -
          A * Complex.I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [complex_inv_re_add_im]
    ring
  have hfirst : IntervalIntegrable
      (fun x : Real => A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul
      (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have hsecond : IntervalIntegrable
      (fun x : Real => A * Complex.I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => hsplit), integral_sub hfirst hsecond,
    mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, integral_self_div_sq_add_sq hy,
    integral_const_div_sq_add_sq hy]

private theorem integral_const_div_re_add_self
    {A : Complex} {x y₁ y₂ : Real} (hx : x ≠ 0) :
    ∫ y : Real in y₁..y₂, A / ((x : Complex) + (y : Complex) * Complex.I) =
      A / Complex.I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 -
        Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
      A / Complex.I * Complex.I *
        (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have hrotate {y : Real} :
      A / ((x : Complex) + (y : Complex) * Complex.I) =
        A / Complex.I /
          ((y : Complex) + ((-x : Real) : Complex) * Complex.I) := by
    have hdenom : (x : Complex) + (y : Complex) * Complex.I ≠ 0 := by
      contrapose! hx
      simpa using congrArg Complex.re hx
    have hrotated :
        (y : Complex) + Complex.I * ((-x : Real) : Complex) ≠ 0 := by
      contrapose! hx
      simpa using congrArg Complex.im hx
    field_simp [hdenom, hrotated]
    push_cast
    ring_nf
    simp
  have hneg : -x ≠ 0 := neg_ne_zero.mpr hx
  simp_rw [hrotate, integral_const_div_self_add_im hneg]

/-- Direct integral of a Cauchy principal part around a rectangle containing
the origin in its interior. -/
theorem guinandWeilRectangleIntegral_const_div_id
    {z w c : Complex}
    (hzre : z.re < 0) (hzim : z.im < 0)
    (hwre : 0 < w.re) (hwim : 0 < w.im) :
    guinandWeilRectangleIntegral (fun s => c / s) z w =
      2 * Complex.I * Real.pi * c := by
  simp only [guinandWeilRectangleIntegral, guinandWeilHorizontalIntegral,
    guinandWeilVerticalIntegral]
  rw [integral_const_div_re_add_self hzre.ne,
    integral_const_div_re_add_self hwre.ne.symm]
  rw [integral_const_div_self_add_im hzim.ne,
    integral_const_div_self_add_im hwim.ne.symm]
  have h₁ : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have h₂ := Real.arctan_inv_of_neg
    (mul_neg_of_pos_of_neg hwre (inv_lt_zero.mpr hzim))
  have h₃ : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have h₄ := Real.arctan_inv_of_neg
    (mul_neg_of_neg_of_pos hzre (inv_pos.mpr hwim))
  have h₅ : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have h₆ := Real.arctan_inv_of_pos
    (mul_pos_of_neg_of_neg hzre (inv_lt_zero.mpr hzim))
  have h₇ : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have h₈ := Real.arctan_inv_of_pos
    (mul_pos hwre (inv_pos.mpr hwim))
  ring_nf
  simp only [one_div, Complex.inv_I, mul_neg, neg_mul, Complex.I_sq,
    neg_neg, Real.arctan_neg, Complex.ofReal_neg, sub_neg_eq_add]
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  ring_nf
  simp only [Complex.I_sq, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_one]
  ring_nf

/-- The normalized integral of `c / (s - p)` is `c` whenever `p` is in the
rectangle interior. -/
theorem guinandWeilNormalizedRectangleIntegral_const_div_sub
    {z w p c : Complex}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hp : Complex.Rectangle z w ∈ 𝓝 p) :
    guinandWeilNormalizedRectangleIntegral (fun s => c / (s - p)) z w = c := by
  rw [guinandWeilRectangle_mem_nhds_iff,
    Set.uIoo_of_le hzre, Set.uIoo_of_le hzim] at hp
  rw [guinandWeilNormalizedRectangleIntegral_translate,
    guinandWeilNormalizedRectangleIntegral]
  have hscale :
      (1 / (2 * (Real.pi : Complex) * Complex.I)) *
        (2 * Complex.I * (Real.pi : Complex) * c) = c := by
    field_simp
  rw [guinandWeilRectangleIntegral_const_div_id]
  · exact hscale
  · simpa using sub_neg.mpr hp.1.1
  · simpa using sub_neg.mpr hp.2.1
  · simpa using sub_pos.mpr hp.1.2
  · simpa using sub_pos.mpr hp.2.2

private theorem cauchyKernel_continuousOn_rectangleBorder
    {z w p c : Complex}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hp : Complex.Rectangle z w ∈ 𝓝 p) :
    ContinuousOn (fun s => c / (s - p)) (guinandWeilRectangleBorder z w) := by
  intro s hs
  have hsp : s ≠ p := by
    intro h
    subst s
    exact not_mem_guinandWeilRectangleBorder_of_rectangle_mem_nhds
      hzre hzim hp hs
  have hanalytic : AnalyticAt Complex (fun u => c / (u - p)) s := by
    fun_prop (disch := exact sub_ne_zero.mpr hsp)
  exact hanalytic.continuousAt.continuousWithinAt

private theorem principalPartSum_borderIntegrable
    {z w : Complex} {S : Finset Complex} {c : Complex → Complex}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hp : ∀ p ∈ S, Complex.Rectangle z w ∈ 𝓝 p) :
    GuinandWeilRectangleBorderIntegrable
      (fun s => ∑ p ∈ S, c p / (s - p)) z w := by
  apply continuousOn_rectangleBorder_integrable
  refine continuousOn_finsetSum _ ?_
  intro p hpS
  exact cauchyKernel_continuousOn_rectangleBorder hzre hzim (hp p hpS)

/-- A finite sum of Cauchy principal parts integrates to the sum of its
coefficients. -/
theorem guinandWeilNormalizedRectangleIntegral_principalPartSum
    {z w : Complex} {S : Finset Complex} {c : Complex → Complex}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hp : ∀ p ∈ S, Complex.Rectangle z w ∈ 𝓝 p) :
    guinandWeilNormalizedRectangleIntegral
        (fun s => ∑ p ∈ S, c p / (s - p)) z w =
      ∑ p ∈ S, c p := by
  classical
  induction S using Finset.cons_induction with
  | empty =>
      simp [guinandWeilNormalizedRectangleIntegral,
        guinandWeilRectangleIntegral, guinandWeilHorizontalIntegral,
        guinandWeilVerticalIntegral]
  | cons p S hnotmem ih =>
      have hpHead : Complex.Rectangle z w ∈ 𝓝 p := hp p (by simp)
      have hpTail : ∀ q ∈ S, Complex.Rectangle z w ∈ 𝓝 q := by
        intro q hq
        exact hp q (by simp [hq])
      have hheadInt : GuinandWeilRectangleBorderIntegrable
          (fun s => c p / (s - p)) z w :=
        continuousOn_rectangleBorder_integrable
          (cauchyKernel_continuousOn_rectangleBorder hzre hzim hpHead)
      have htailInt := principalPartSum_borderIntegrable
        (c := c) hzre hzim hpTail
      simp_rw [Finset.sum_cons]
      rw [guinandWeilNormalizedRectangleIntegral_add hheadInt htailInt,
        guinandWeilNormalizedRectangleIntegral_const_div_sub hzre hzim hpHead,
        ih hpTail]

/-- Finite rectangle residue theorem in analytic-remainder form.  The theorem
contains no formula-specific assumption: all singular content is an explicit
finite principal part, while the remainder is proved analytic. -/
theorem guinandWeilNormalizedRectangleIntegral_eq_sum_of_analyticRemainder
    {F G : Complex → Complex} {z w : Complex}
    {S : Finset Complex} {c : Complex → Complex}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hp : ∀ p ∈ S, Complex.Rectangle z w ∈ 𝓝 p)
    (hG : DifferentiableOn Complex G (Complex.Rectangle z w))
    (hboundary : Set.EqOn F
      (fun s => G s + ∑ p ∈ S, c p / (s - p))
      (guinandWeilRectangleBorder z w)) :
    guinandWeilNormalizedRectangleIntegral F z w =
      ∑ p ∈ S, c p := by
  rw [guinandWeilNormalizedRectangleIntegral_congr hboundary]
  have hGInt : GuinandWeilRectangleBorderIntegrable G z w :=
    continuousOn_rectangleBorder_integrable
      (hG.continuousOn.mono (guinandWeilRectangleBorder_subset_rectangle z w))
  have hprincipalInt := principalPartSum_borderIntegrable
    (c := c) hzre hzim hp
  rw [guinandWeilNormalizedRectangleIntegral_add hGInt hprincipalInt,
    guinandWeilNormalizedRectangleIntegral_eq_zero_of_differentiableOn hG,
    zero_add,
    guinandWeilNormalizedRectangleIntegral_principalPartSum hzre hzim hp]

end

end RiemannHypothesisProject
