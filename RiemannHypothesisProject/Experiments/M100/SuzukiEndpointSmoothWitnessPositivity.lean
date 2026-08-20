import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointSmoothTransformVariation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Smooth-kernel witness positivity for M100-DF6D4

This module proves the frozen-interval positivity input left visible by the
smooth-transform variation bridge.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set

def suzukiRThirdExponentialWitnessFirst (t : Real) : Real :=
  Real.exp (3 * t / 2) * (t + 3 * t ^ 2 / 4) +
    Real.exp (-t / 2) * (3 * t - 3 * t ^ 2 / 4) -
      2 * Real.sinh (2 * t)

def suzukiRThirdExponentialWitnessSecond (t : Real) : Real :=
  Real.exp (3 * t / 2) * (1 + 3 * t + 9 * t ^ 2 / 8) +
    Real.exp (-t / 2) * (3 - 3 * t + 3 * t ^ 2 / 8) -
      4 * Real.cosh (2 * t)

def suzukiRThirdExponentialWitnessThird (t : Real) : Real :=
  Real.exp (3 * t / 2) * (9 / 2 + 27 * t / 4 + 27 * t ^ 2 / 16) +
    Real.exp (-t / 2) * (-9 / 2 + 9 * t / 4 - 3 * t ^ 2 / 16) -
      8 * Real.sinh (2 * t)

def suzukiRThirdExponentialWitnessFourth (t : Real) : Real :=
  Real.exp (3 * t / 2) * (27 / 2 + 27 * t / 2 + 81 * t ^ 2 / 32) +
    Real.exp (-t / 2) * (9 / 2 - 3 * t / 2 + 3 * t ^ 2 / 32) -
      16 * Real.cosh (2 * t)

def suzukiRThirdExponentialWitnessFifth (t : Real) : Real :=
  Real.exp (3 * t / 2) * (135 / 4 + 405 * t / 16 + 243 * t ^ 2 / 64) +
    Real.exp (-t / 2) * (-15 / 4 + 15 * t / 16 - 3 * t ^ 2 / 64) -
      32 * Real.sinh (2 * t)

private theorem hasDerivAt_exp_three_halves (t : Real) :
    HasDerivAt (fun x : Real => Real.exp (3 * x / 2))
      (3 / 2 * Real.exp (3 * t / 2)) t := by
  have h := (Real.hasDerivAt_exp (3 * t / 2)).comp t
    (((hasDerivAt_id t).const_mul 3).div_const 2)
  have heq :
      (Real.exp ∘ fun x : Real => 3 * id x / 2) =ᶠ[nhds t]
        fun x : Real => Real.exp (3 * x / 2) := by
    filter_upwards with x
    rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

private theorem hasDerivAt_exp_neg_half (t : Real) :
    HasDerivAt (fun x : Real => Real.exp (-x / 2))
      (-1 / 2 * Real.exp (-t / 2)) t := by
  have h := (Real.hasDerivAt_exp (-t / 2)).comp t
    (((hasDerivAt_id t).neg).div_const 2)
  have heq :
      (Real.exp ∘ fun x : Real => (-id) x / 2) =ᶠ[nhds t]
        fun x : Real => Real.exp (-x / 2) := by
    filter_upwards with x
    rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

private theorem hasDerivAt_sinh_two (t : Real) :
    HasDerivAt (fun x : Real => Real.sinh (2 * x))
      (2 * Real.cosh (2 * t)) t := by
  have h := (Real.hasDerivAt_sinh (2 * t)).comp t
    ((hasDerivAt_id t).const_mul 2)
  have heq :
      (Real.sinh ∘ fun x : Real => 2 * id x) =ᶠ[nhds t]
        fun x : Real => Real.sinh (2 * x) := by
    filter_upwards with x
    rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

private theorem hasDerivAt_cosh_two (t : Real) :
    HasDerivAt (fun x : Real => Real.cosh (2 * x))
      (2 * Real.sinh (2 * t)) t := by
  have h := (Real.hasDerivAt_cosh (2 * t)).comp t
    ((hasDerivAt_id t).const_mul 2)
  have heq :
      (Real.cosh ∘ fun x : Real => 2 * id x) =ᶠ[nhds t]
        fun x : Real => Real.cosh (2 * x) := by
    filter_upwards with x
    rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

theorem hasDerivAt_suzukiRThirdExponentialWitness (t : Real) :
    HasDerivAt suzukiRThirdExponentialWitness
      (suzukiRThirdExponentialWitnessFirst t) t := by
  have hExpPos :
      HasDerivAt (fun x : Real => Real.exp (3 * x / 2))
        (3 / 2 * Real.exp (3 * t / 2)) t := by
    have h := (Real.hasDerivAt_exp (3 * t / 2)).comp t
      (((hasDerivAt_id t).const_mul 3).div_const 2)
    have heq :
        (Real.exp ∘ fun x : Real => 3 * id x / 2) =ᶠ[nhds t]
          fun x : Real => Real.exp (3 * x / 2) := by
      filter_upwards with x
      rfl
    exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)
  have hExpNeg :
      HasDerivAt (fun x : Real => Real.exp (-x / 2))
        (-1 / 2 * Real.exp (-t / 2)) t := by
    have h := (Real.hasDerivAt_exp (-t / 2)).comp t
      (((hasDerivAt_id t).neg).div_const 2)
    have heq :
        (Real.exp ∘ fun x : Real => (-id) x / 2) =ᶠ[nhds t]
          fun x : Real => Real.exp (-x / 2) := by
      filter_upwards with x
      rfl
    exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)
  have hCosh :
      HasDerivAt (fun x : Real => Real.cosh (2 * x))
        (2 * Real.sinh (2 * t)) t := by
    have h := (Real.hasDerivAt_cosh (2 * t)).comp t
      ((hasDerivAt_id t).const_mul 2)
    have heq :
        (Real.cosh ∘ fun x : Real => 2 * id x) =ᶠ[nhds t]
          fun x : Real => Real.cosh (2 * x) := by
      filter_upwards with x
      rfl
    exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)
  have h :=
    (((hasDerivAt_id t).pow 2).div_const 2).mul
      (hExpPos.add (hExpNeg.const_mul 3)) |>.sub hCosh |>.add_const 1
  unfold suzukiRThirdExponentialWitness
    suzukiRThirdExponentialWitnessFirst
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with x
    rfl
  · norm_num
    ring

theorem hasDerivAt_suzukiRThirdExponentialWitnessFirst (t : Real) :
    HasDerivAt suzukiRThirdExponentialWitnessFirst
      (suzukiRThirdExponentialWitnessSecond t) t := by
  have hPolyPos := (hasDerivAt_id t).add
    (((hasDerivAt_pow 2 t).const_mul 3).div_const 4)
  have hPolyNeg := ((hasDerivAt_id t).const_mul 3).sub
    (((hasDerivAt_pow 2 t).const_mul 3).div_const 4)
  have h :=
    (hasDerivAt_exp_three_halves t).mul hPolyPos |>.add
      ((hasDerivAt_exp_neg_half t).mul hPolyNeg) |>.sub
        ((hasDerivAt_sinh_two t).const_mul 2)
  unfold suzukiRThirdExponentialWitnessFirst
    suzukiRThirdExponentialWitnessSecond
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with x
    rfl
  · norm_num
    ring

theorem hasDerivAt_suzukiRThirdExponentialWitnessSecond (t : Real) :
    HasDerivAt suzukiRThirdExponentialWitnessSecond
      (suzukiRThirdExponentialWitnessThird t) t := by
  have hPolyPos :=
    (hasDerivAt_const t (1 : Real)).add ((hasDerivAt_id t).const_mul 3) |>.add
      (((hasDerivAt_pow 2 t).const_mul 9).div_const 8)
  have hPolyNeg :=
    (hasDerivAt_const t (3 : Real)).sub ((hasDerivAt_id t).const_mul 3) |>.add
      (((hasDerivAt_pow 2 t).const_mul 3).div_const 8)
  have h :=
    (hasDerivAt_exp_three_halves t).mul hPolyPos |>.add
      ((hasDerivAt_exp_neg_half t).mul hPolyNeg) |>.sub
        ((hasDerivAt_cosh_two t).const_mul 4)
  unfold suzukiRThirdExponentialWitnessSecond
    suzukiRThirdExponentialWitnessThird
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with x
    rfl
  · norm_num
    ring

theorem hasDerivAt_suzukiRThirdExponentialWitnessThird (t : Real) :
    HasDerivAt suzukiRThirdExponentialWitnessThird
      (suzukiRThirdExponentialWitnessFourth t) t := by
  have hPolyPos :=
    (hasDerivAt_const t (9 / 2 : Real)).add
      (((hasDerivAt_id t).const_mul 27).div_const 4) |>.add
        (((hasDerivAt_pow 2 t).const_mul 27).div_const 16)
  have hPolyNeg :=
    (hasDerivAt_const t (-9 / 2 : Real)).add
      (((hasDerivAt_id t).const_mul 9).div_const 4) |>.sub
        (((hasDerivAt_pow 2 t).const_mul 3).div_const 16)
  have h :=
    (hasDerivAt_exp_three_halves t).mul hPolyPos |>.add
      ((hasDerivAt_exp_neg_half t).mul hPolyNeg) |>.sub
        ((hasDerivAt_sinh_two t).const_mul 8)
  unfold suzukiRThirdExponentialWitnessThird
    suzukiRThirdExponentialWitnessFourth
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with x
    rfl
  · norm_num
    ring

theorem hasDerivAt_suzukiRThirdExponentialWitnessFourth (t : Real) :
    HasDerivAt suzukiRThirdExponentialWitnessFourth
      (suzukiRThirdExponentialWitnessFifth t) t := by
  have hPolyPos :=
    (hasDerivAt_const t (27 / 2 : Real)).add
      (((hasDerivAt_id t).const_mul 27).div_const 2) |>.add
        (((hasDerivAt_pow 2 t).const_mul 81).div_const 32)
  have hPolyNeg :=
    (hasDerivAt_const t (9 / 2 : Real)).sub
      (((hasDerivAt_id t).const_mul 3).div_const 2) |>.add
        (((hasDerivAt_pow 2 t).const_mul 3).div_const 32)
  have h :=
    (hasDerivAt_exp_three_halves t).mul hPolyPos |>.add
      ((hasDerivAt_exp_neg_half t).mul hPolyNeg) |>.sub
        ((hasDerivAt_cosh_two t).const_mul 16)
  unfold suzukiRThirdExponentialWitnessFourth
    suzukiRThirdExponentialWitnessFifth
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with x
    rfl
  · norm_num
    ring

private theorem exp_half_le_one_add_of_mem_Icc
    {t : Real} (ht : t ∈ Icc (0 : Real) 1) :
    Real.exp (t / 2) ≤ 1 + t := by
  have hhalf0 : 0 ≤ t / 2 := by linarith [ht.1]
  have hhalf1 : t / 2 < 1 := by linarith [ht.2]
  have hexp := Real.exp_bound_div_one_sub_of_interval hhalf0 hhalf1
  have hden : 0 < 1 - t / 2 := by linarith
  have hproduct : 0 ≤ t * (1 - t) :=
    mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have hfraction : 1 / (1 - t / 2) ≤ 1 + t := by
    rw [div_le_iff₀ hden]
    nlinarith
  exact hexp.trans hfraction

theorem suzukiRThirdExponentialWitnessFifth_nonneg_of_mem_Icc
    {t : Real} (ht : t ∈ Icc (0 : Real) 1) :
    0 ≤ suzukiRThirdExponentialWitnessFifth t := by
  have hExpHalf := exp_half_le_one_add_of_mem_Icc ht
  have hExpMainPos : 0 < Real.exp (3 * t / 2) := Real.exp_pos _
  have hExpMainOne : 1 ≤ Real.exp (3 * t / 2) := by
    rw [Real.one_le_exp_iff]
    linarith [ht.1]
  have hSinh : Real.sinh (2 * t) ≤ Real.exp (2 * t) / 2 := by
    rw [Real.sinh_eq]
    have := Real.exp_pos (-(2 * t))
    linarith
  have hMainBracket :
      (71 / 4 : Real) ≤
        (135 / 4 + 405 * t / 16 + 243 * t ^ 2 / 64) -
          16 * Real.exp (t / 2) := by
    have hscaled := mul_le_mul_of_nonneg_left hExpHalf
      (by norm_num : (0 : Real) ≤ 16)
    have hlinear : 0 ≤ (149 / 16 : Real) * t :=
      mul_nonneg (by norm_num) ht.1
    have hsquare : 0 ≤ (243 / 64 : Real) * t ^ 2 := by positivity
    linarith
  have hMainBracketNonneg :
      0 ≤ (135 / 4 + 405 * t / 16 + 243 * t ^ 2 / 64) -
        16 * Real.exp (t / 2) := by
    linarith
  have hMainProduct :
      (71 / 4 : Real) ≤ Real.exp (3 * t / 2) *
        ((135 / 4 + 405 * t / 16 + 243 * t ^ 2 / 64) -
          16 * Real.exp (t / 2)) := by
    have hmul := mul_le_mul hMainBracket hExpMainOne
      (by norm_num : (0 : Real) ≤ 1) hMainBracketNonneg
    norm_num at hmul ⊢
    simpa [mul_comm] using hmul
  have hExpSplit :
      Real.exp (2 * t) =
        Real.exp (3 * t / 2) * Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hMain :
      (71 / 4 : Real) ≤
        Real.exp (3 * t / 2) *
            (135 / 4 + 405 * t / 16 + 243 * t ^ 2 / 64) -
          32 * Real.sinh (2 * t) := by
    rw [hExpSplit] at hSinh
    nlinarith
  have hExpNegHalf : Real.exp (-t / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [ht.1]
  have hNegBracketNonpos :
      (-15 / 4 + 15 * t / 16 - 3 * t ^ 2 / 64 : Real) ≤ 0 := by
    have hlinear := mul_le_mul_of_nonneg_left ht.2
      (by norm_num : (0 : Real) ≤ 15 / 16)
    nlinarith [sq_nonneg t]
  have hNegBracketLower :
      (-15 / 4 : Real) ≤ -15 / 4 + 15 * t / 16 - 3 * t ^ 2 / 64 := by
    have hproduct : 0 ≤ t * (20 - t) := by
      apply mul_nonneg ht.1
      linarith [ht.2]
    nlinarith
  have hNegProduct :
      (-15 / 4 : Real) ≤ Real.exp (-t / 2) *
        (-15 / 4 + 15 * t / 16 - 3 * t ^ 2 / 64) := by
    have hscale := mul_le_mul_of_nonpos_right hExpNegHalf hNegBracketNonpos
    nlinarith
  unfold suzukiRThirdExponentialWitnessFifth
  linarith

@[simp] theorem suzukiRThirdExponentialWitness_zero :
    suzukiRThirdExponentialWitness 0 = 0 := by
  norm_num [suzukiRThirdExponentialWitness]

@[simp] theorem suzukiRThirdExponentialWitnessFirst_zero :
    suzukiRThirdExponentialWitnessFirst 0 = 0 := by
  norm_num [suzukiRThirdExponentialWitnessFirst]

@[simp] theorem suzukiRThirdExponentialWitnessSecond_zero :
    suzukiRThirdExponentialWitnessSecond 0 = 0 := by
  norm_num [suzukiRThirdExponentialWitnessSecond]

@[simp] theorem suzukiRThirdExponentialWitnessThird_zero :
    suzukiRThirdExponentialWitnessThird 0 = 0 := by
  norm_num [suzukiRThirdExponentialWitnessThird]

@[simp] theorem suzukiRThirdExponentialWitnessFourth_zero :
    suzukiRThirdExponentialWitnessFourth 0 = 2 := by
  norm_num [suzukiRThirdExponentialWitnessFourth]

private theorem nonneg_of_hasDerivAt_nonneg_on_Icc
    {f f' : Real → Real}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hzero : 0 ≤ f 0)
    (hderivNonneg : ∀ x ∈ Icc (0 : Real) 1, 0 ≤ f' x)
    {t : Real} (ht : t ∈ Icc (0 : Real) 1) :
    0 ≤ f t := by
  have hdiff : Differentiable Real f := fun x => (hderiv x).differentiableAt
  have hmono : MonotoneOn f (Icc (0 : Real) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : Real) 1)
      hdiff.continuous.continuousOn hdiff.differentiableOn
    intro x hx
    rw [(hderiv x).deriv]
    exact hderivNonneg x (interior_subset hx)
  exact hzero.trans (hmono (by norm_num) ht ht.1)

theorem suzukiRThirdExponentialWitnessFourth_nonneg_of_mem_Icc
    {t : Real} (ht : t ∈ Icc (0 : Real) 1) :
    0 ≤ suzukiRThirdExponentialWitnessFourth t := by
  apply nonneg_of_hasDerivAt_nonneg_on_Icc
    hasDerivAt_suzukiRThirdExponentialWitnessFourth (by norm_num) _ ht
  intro x hx
  exact suzukiRThirdExponentialWitnessFifth_nonneg_of_mem_Icc hx

theorem suzukiRThirdExponentialWitnessThird_nonneg_of_mem_Icc
    {t : Real} (ht : t ∈ Icc (0 : Real) 1) :
    0 ≤ suzukiRThirdExponentialWitnessThird t := by
  apply nonneg_of_hasDerivAt_nonneg_on_Icc
    hasDerivAt_suzukiRThirdExponentialWitnessThird (by norm_num) _ ht
  intro x hx
  exact suzukiRThirdExponentialWitnessFourth_nonneg_of_mem_Icc hx

theorem suzukiRThirdExponentialWitnessSecond_nonneg_of_mem_Icc
    {t : Real} (ht : t ∈ Icc (0 : Real) 1) :
    0 ≤ suzukiRThirdExponentialWitnessSecond t := by
  apply nonneg_of_hasDerivAt_nonneg_on_Icc
    hasDerivAt_suzukiRThirdExponentialWitnessSecond (by norm_num) _ ht
  intro x hx
  exact suzukiRThirdExponentialWitnessThird_nonneg_of_mem_Icc hx

theorem suzukiRThirdExponentialWitnessFirst_nonneg_of_mem_Icc
    {t : Real} (ht : t ∈ Icc (0 : Real) 1) :
    0 ≤ suzukiRThirdExponentialWitnessFirst t := by
  apply nonneg_of_hasDerivAt_nonneg_on_Icc
    hasDerivAt_suzukiRThirdExponentialWitnessFirst (by norm_num) _ ht
  intro x hx
  exact suzukiRThirdExponentialWitnessSecond_nonneg_of_mem_Icc hx

theorem suzukiRThirdExponentialWitness_nonneg_of_mem_Icc
    {t : Real} (ht : t ∈ Icc (0 : Real) 1) :
    0 ≤ suzukiRThirdExponentialWitness t := by
  apply nonneg_of_hasDerivAt_nonneg_on_Icc
    hasDerivAt_suzukiRThirdExponentialWitness (by norm_num) _ ht
  intro x hx
  exact suzukiRThirdExponentialWitnessFirst_nonneg_of_mem_Icc hx

private theorem two_mul_suzukiProjectAStar_le_one :
    2 * suzukiProjectAStar ≤ 1 := by
  have hA := fineAStarInterval_contains
  have hAUpper :
      suzukiProjectAStar ≤
        (42867814670054957 / 100000000000000000 : Real) := by
    simpa [fineAStarInterval, RationalInterval.Contains] using hA.2
  linarith

theorem suzukiRThirdExponentialWitness_nonneg_on_project_interval
    {t : Real} (ht : t ∈ Ioc (0 : Real) (2 * suzukiProjectAStar)) :
    0 ≤ suzukiRThirdExponentialWitness t := by
  apply suzukiRThirdExponentialWitness_nonneg_of_mem_Icc
  exact ⟨ht.1.le, ht.2.trans two_mul_suzukiProjectAStar_le_one⟩

theorem suzukiRThirdKernel_nonpos_on_project_interval
    {t : Real} (ht : t ∈ Ioc (0 : Real) (2 * suzukiProjectAStar)) :
    suzukiRThirdKernel t ≤ 0 := by
  exact suzukiRThirdKernel_nonpos_of_exponentialWitness_nonneg ht.1
    (suzukiRThirdExponentialWitness_nonneg_on_project_interval ht)

/-- With witness positivity discharged, the exact transform identity is the
only remaining premise for the smooth DF6D4 coefficient estimate. -/
theorem suzukiDF6D4SmoothTransformDifference_abs_le_of_transformIdentity
    (mode : Nat) (hmode : 1 ≤ mode)
    (htransform :
      suzukiDF6D4SmoothTransformDifference mode =
        -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiRSecondKernel t *
            Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t))) :
    |suzukiDF6D4SmoothTransformDifference mode| ≤
      (2 * suzukiDF6D4DF0RemainderVariation * suzukiProjectAStar /
        Real.pi) / mode := by
  exact suzukiDF6D4SmoothTransformDifference_abs_le_of_kernelVariation
    mode hmode htransform fun _ ht =>
      suzukiRThirdKernel_nonpos_on_project_interval ht

end

end RiemannHypothesisProject.Experiments.M100
