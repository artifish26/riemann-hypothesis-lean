import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25SpectralReduction
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The quarter-point digamma normalization in Suzuki's Gamma kernel

This module evaluates the scalar base point left visible by the equation-(2.5)
spectral reduction.  The proof uses only Legendre's duplication formula,
Euler's reflection formula, and the already formalized value of the digamma
function at `1 / 2`.

This is an elementary normalization bridge.  It does not assert the remaining
regular-Gamma kernel identity.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open RiemannHypothesisProject.ComplexCompactExhaustion

private def suzukiLogGammaDeriv (x : Real) : Real :=
  deriv (Real.log ∘ Real.Gamma) x

private theorem differentiableAt_realGamma_of_pos {x : Real} (hx : 0 < x) :
    DifferentiableAt Real Real.Gamma x :=
  Real.differentiableAt_Gamma (fun m => by
    have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
    linarith)

private theorem differentiableAt_suzukiLogGammaDeriv_source
    {x : Real} (hx : 0 < x) :
    DifferentiableAt Real (Real.log ∘ Real.Gamma) x := by
  exact (differentiableAt_realGamma_of_pos hx).log
    (Real.Gamma_ne_zero (fun m => by
      have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
      linarith))

private theorem hasDerivAt_suzukiLogGamma_comp_affine
    (x a b : Real) (hpos : 0 < a * x + b) :
    HasDerivAt
      (fun t : Real => (Real.log ∘ Real.Gamma) (a * t + b))
      (a * suzukiLogGammaDeriv (a * x + b)) x := by
  have hinner : HasDerivAt (fun t : Real => a * t + b) a x := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id x).const_mul a).add_const b
  have hcomp := HasDerivAt.comp x
    (differentiableAt_suzukiLogGammaDeriv_source hpos).hasDerivAt hinner
  simpa only [Function.comp_def, suzukiLogGammaDeriv, mul_comm] using hcomp

private theorem suzukiLogGammaDeriv_one_half :
    suzukiLogGammaDeriv (1 / 2) =
      -2 * Real.log 2 - Real.eulerMascheroniConstant := by
  have hbase := congrArg Complex.re
    (digamma_ofReal_eq_deriv_logGamma
      (x := (1 / 2 : Real)) (by norm_num))
  have hhalf : Complex.digamma (((1 / 2 : Real) : Complex)) =
      -2 * Complex.log 2 - Real.eulerMascheroniConstant := by
    convert Complex.digamma_one_half using 1 <;> norm_num
  rw [hhalf] at hbase
  have hlog : (Complex.log (2 : Complex)).re = Real.log 2 := by
    simpa using Complex.log_ofReal_re 2
  norm_num [Complex.sub_re, Complex.mul_re] at hbase
  rw [hlog] at hbase
  simpa [suzukiLogGammaDeriv, Complex.log_ofReal_re] using hbase.symm

private theorem suzukiLogGammaDeriv_quarter_add_three_quarters :
    suzukiLogGammaDeriv (1 / 4) + suzukiLogGammaDeriv (3 / 4) =
      -2 * Real.eulerMascheroniConstant - 6 * Real.log 2 := by
  let f := Real.log ∘ Real.Gamma
  have hidentity {x : Real} (hx : 0 < x) :
      f x + f (x + 1 / 2) =
        f (2 * x) + (1 - 2 * x) * Real.log 2 +
          Real.log (Real.sqrt Real.pi) := by
    have hxHalf : 0 < x + 1 / 2 := by linarith
    have hxTwo : 0 < 2 * x := by positivity
    have hGammaX : Real.Gamma x ≠ 0 := Real.Gamma_ne_zero (fun m => by
      have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
      linarith)
    have hGammaHalf : Real.Gamma (x + 1 / 2) ≠ 0 :=
      Real.Gamma_ne_zero (fun m => by
      have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
      linarith)
    have hGammaTwo : Real.Gamma (2 * x) ≠ 0 :=
      Real.Gamma_ne_zero (fun m => by
      have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
      linarith)
    have hpow : (2 : Real) ^ (1 - 2 * x) ≠ 0 := by positivity
    have hsqrt : Real.sqrt Real.pi ≠ 0 :=
      Real.sqrt_ne_zero'.mpr Real.pi_pos
    dsimp only [f, Function.comp_apply]
    rw [← Real.log_mul hGammaX hGammaHalf,
      Real.Gamma_mul_Gamma_add_half,
      Real.log_mul (mul_ne_zero hGammaTwo hpow) hsqrt,
      Real.log_mul hGammaTwo hpow,
      Real.log_rpow (by norm_num : (0 : Real) < 2)]
  have hlocal :
      (fun x : Real => f x + f (x + 1 / 2)) =ᶠ[nhds (1 / 4 : Real)]
        (fun x : Real =>
          f (2 * x) + (1 - 2 * x) * Real.log 2 +
            Real.log (Real.sqrt Real.pi)) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0 : Real) < 1 / 4)]
      with x hx
    exact hidentity hx
  have hq : (0 : Real) < 1 / 4 := by norm_num
  have hthree : (0 : Real) < 3 / 4 := by norm_num
  have hhalf : (0 : Real) < 1 / 2 := by norm_num
  have hlhsDeriv :
      deriv (fun x : Real => f x + f (x + 1 / 2)) (1 / 4) =
        suzukiLogGammaDeriv (1 / 4) +
          suzukiLogGammaDeriv (3 / 4) := by
    have h₁ := hasDerivAt_suzukiLogGamma_comp_affine
      (1 / 4) 1 0 (by norm_num)
    have h₃ := hasDerivAt_suzukiLogGamma_comp_affine
      (1 / 4) 1 (1 / 2) (by norm_num)
    have h := (h₁.add h₃).deriv
    have hfun :
        ((fun t : Real => (Real.log ∘ Real.Gamma) (1 * t + 0)) +
          (fun t => (Real.log ∘ Real.Gamma) (1 * t + 1 / 2))) =
          (fun x : Real => f x + f (x + 1 / 2)) := by
      funext x
      simp only [Pi.add_apply, f, one_mul, add_zero]
    rw [hfun] at h
    simpa only [one_mul, add_zero,
      show (1 / 4 : Real) + 1 / 2 = 3 / 4 by norm_num] using h
  have htwo : HasDerivAt (fun x : Real => f (2 * x))
      (2 * suzukiLogGammaDeriv (1 / 2)) (1 / 4) := by
    have h := hasDerivAt_suzukiLogGamma_comp_affine
      (1 / 4) 2 0 (by norm_num)
    simpa only [f, Function.comp_def, add_zero,
      show (2 : Real) * (1 / 4) = 1 / 2 by norm_num] using h
  have hlinear : HasDerivAt
      (fun x : Real => (1 - 2 * x) * Real.log 2)
      (-2 * Real.log 2) (1 / 4) := by
    simpa only [Pi.sub_apply, id_eq, mul_one, zero_sub] using
      (((hasDerivAt_const (1 / 4 : Real) 1).sub
      ((hasDerivAt_id (1 / 4 : Real)).const_mul 2)).mul_const
        (Real.log 2))
  have hrhsDeriv :
      deriv (fun x : Real =>
        f (2 * x) + (1 - 2 * x) * Real.log 2 +
          Real.log (Real.sqrt Real.pi)) (1 / 4) =
        2 * suzukiLogGammaDeriv (1 / 2) - 2 * Real.log 2 := by
    have h := ((htwo.add hlinear).add_const
      (Real.log (Real.sqrt Real.pi))).deriv
    change deriv (fun x : Real =>
      f (2 * x) + (1 - 2 * x) * Real.log 2 +
        Real.log (Real.sqrt Real.pi)) (1 / 4) = _ at h
    simpa only [sub_eq_add_neg, neg_mul] using h
  have hderiv := Filter.EventuallyEq.deriv_eq hlocal
  rw [hlhsDeriv, hrhsDeriv] at hderiv
  rw [suzukiLogGammaDeriv_one_half] at hderiv
  linarith

private theorem suzukiLogGammaDeriv_quarter_sub_three_quarters :
    suzukiLogGammaDeriv (1 / 4) - suzukiLogGammaDeriv (3 / 4) =
      -Real.pi := by
  let f := Real.log ∘ Real.Gamma
  have hidentity {x : Real} (hx : 0 < x) (hxOne : x < 1) :
      f x + f (1 - x) =
        Real.log Real.pi - Real.log (Real.sin (Real.pi * x)) := by
    have hxComp : 0 < 1 - x := by linarith
    have hGammaX : Real.Gamma x ≠ 0 := Real.Gamma_ne_zero (fun m => by
      have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
      linarith)
    have hGammaComp : Real.Gamma (1 - x) ≠ 0 :=
      Real.Gamma_ne_zero (fun m => by
      have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
      linarith)
    have hsinPos : 0 < Real.sin (Real.pi * x) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hx) (by
        nlinarith [Real.pi_pos])
    dsimp only [f, Function.comp_apply]
    rw [← Real.log_mul hGammaX hGammaComp,
      Real.Gamma_mul_Gamma_one_sub,
      Real.log_div Real.pi_ne_zero hsinPos.ne']
  have hlocal :
      (fun x : Real => f x + f (-x + 1)) =ᶠ[nhds (1 / 4 : Real)]
        (fun x : Real =>
          Real.log Real.pi - Real.log (Real.sin (Real.pi * x))) := by
    filter_upwards
      [eventually_gt_nhds (by norm_num : (0 : Real) < 1 / 4),
        eventually_lt_nhds (by norm_num : (1 / 4 : Real) < 1)] with x hx hxOne
    convert hidentity hx hxOne using 1 <;> ring
  have hq : (0 : Real) < 1 / 4 := by norm_num
  have hthree : (0 : Real) < 3 / 4 := by norm_num
  have hlhsDeriv :
      deriv (fun x : Real => f x + f (-x + 1)) (1 / 4) =
        suzukiLogGammaDeriv (1 / 4) -
          suzukiLogGammaDeriv (3 / 4) := by
    have h₁ := hasDerivAt_suzukiLogGamma_comp_affine
      (1 / 4) 1 0 (by norm_num)
    have h₃ := hasDerivAt_suzukiLogGamma_comp_affine
      (1 / 4) (-1) 1 (by norm_num)
    have h := (h₁.add h₃).deriv
    have hfun :
        ((fun t : Real => (Real.log ∘ Real.Gamma) (1 * t + 0)) +
          (fun t => (Real.log ∘ Real.Gamma) (-1 * t + 1))) =
          (fun x : Real => f x + f (-x + 1)) := by
      funext x
      simp only [Pi.add_apply, f, one_mul, add_zero, neg_mul]
    rw [hfun] at h
    simpa only [one_mul, add_zero,
      show (-1 : Real) * (1 / 4) + 1 = 3 / 4 by norm_num,
      show -(1 / 4 : Real) + 1 = 3 / 4 by norm_num,
      neg_mul, sub_eq_add_neg] using h
  have hsin : HasDerivAt (fun x : Real => Real.sin (Real.pi * x))
      (Real.cos (Real.pi * (1 / 4)) * Real.pi) (1 / 4) := by
    have hinner : HasDerivAt (fun x : Real => Real.pi * x)
        Real.pi (1 / 4) := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id (1 / 4 : Real)).const_mul Real.pi
    exact (Real.hasDerivAt_sin (Real.pi * (1 / 4))).comp
      (1 / 4 : Real) hinner
  have hsinNe : Real.sin (Real.pi * (1 / 4)) ≠ 0 := by
    rw [show Real.pi * (1 / 4 : Real) = Real.pi / 4 by ring,
      Real.sin_pi_div_four]
    positivity
  have hrhsRawDeriv :
      deriv (fun x : Real =>
        Real.log Real.pi - Real.log (Real.sin (Real.pi * x))) (1 / 4) =
        -(Real.cos (Real.pi * (1 / 4)) * Real.pi /
          Real.sin (Real.pi * (1 / 4))) := by
    have h := ((hasDerivAt_const (1 / 4 : Real) (Real.log Real.pi)).sub
      (hsin.log hsinNe)).deriv
    change deriv (fun x : Real =>
      Real.log Real.pi - Real.log (Real.sin (Real.pi * x))) (1 / 4) = _ at h
    simpa only [zero_sub] using h
  have htrig :
      -(Real.cos (Real.pi * (1 / 4)) * Real.pi /
          Real.sin (Real.pi * (1 / 4))) = -Real.pi := by
    rw [show Real.pi * (1 / 4 : Real) = Real.pi / 4 by ring,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    have hsqrt : Real.sqrt 2 / 2 ≠ 0 := by positivity
    field_simp [hsqrt]
  have hrhsDeriv :
      deriv (fun x : Real =>
        Real.log Real.pi - Real.log (Real.sin (Real.pi * x))) (1 / 4) =
        -Real.pi := by
    rw [hrhsRawDeriv, htrig]
  have hderiv := Filter.EventuallyEq.deriv_eq hlocal
  rw [hlhsDeriv, hrhsDeriv] at hderiv
  exact hderiv

/-- The quarter-point digamma value fixing Suzuki's Archimedean base
coefficient. -/
theorem suzuki_digamma_one_fourth :
    Complex.digamma (1 / 4 : Complex) =
      ((-Real.eulerMascheroniConstant - Real.pi / 2 -
        3 * Real.log 2 : Real) : Complex) := by
  have hbase := digamma_ofReal_eq_deriv_logGamma
    (x := (1 / 4 : Real)) (by norm_num)
  calc
    Complex.digamma (1 / 4 : Complex) =
        ((suzukiLogGammaDeriv (1 / 4) : Real) : Complex) := by
      convert hbase using 1
      · norm_num
      · rfl
    _ = ((-Real.eulerMascheroniConstant - Real.pi / 2 -
          3 * Real.log 2 : Real) : Complex) := by
      congr 1
      have hadd := suzukiLogGammaDeriv_quarter_add_three_quarters
      have hsub := suzukiLogGammaDeriv_quarter_sub_three_quarters
      linarith

/-- Project-normalized form of the Archimedean base coefficient. -/
theorem suzukiGammaBaseCoefficient_eq :
    suzukiGammaBaseCoefficient =
      -Real.eulerMascheroniConstant - Real.pi / 2 -
        3 * Real.log 2 - Real.log Real.pi := by
  unfold suzukiGammaBaseCoefficient
  rw [suzuki_digamma_one_fourth]
  simp only [Complex.ofReal_re]

/-- The base coefficient differs from the visible equation-(2.5) scalar by
exactly the elementary quarter-point restoration constant. -/
theorem suzukiGammaBaseCoefficient_sub_completeScalar :
    suzukiGammaBaseCoefficient - suzukiProjectCompleteScalar =
      -Real.pi / 2 - 2 * Real.log 2 := by
  rw [suzukiGammaBaseCoefficient_eq]
  unfold suzukiProjectCompleteScalar suzukiSourceLogNormalizationConstant
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) Real.pi_ne_zero]
  ring

end

end M100
end Experiments
end RiemannHypothesisProject
