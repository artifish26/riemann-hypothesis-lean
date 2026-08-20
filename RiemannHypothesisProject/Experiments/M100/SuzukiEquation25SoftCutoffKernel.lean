import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25AbelHardProfile

/-!
# Exponential soft cutoff for Suzuki's equation (2.5)

The removable exponential quotient is represented as a finite integral.  In
this form continuity, evenness, and the uniform bound are immediate, while
away from the origin it is the expected soft reciprocal cutoff.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory

/-- The continuous exponential regularization of `-1 / (2 |t|)`. -/
def suzukiEquation25SoftReciprocalKernel (lam t : Real) : Real :=
  -(1 / 2) * ∫ s in (0 : Real)..lam, Real.exp (-s * |t|)

theorem continuous_suzukiEquation25SoftReciprocalKernel (lam : Real) :
    Continuous (suzukiEquation25SoftReciprocalKernel lam) := by
  unfold suzukiEquation25SoftReciprocalKernel
  fun_prop

@[simp]
theorem suzukiEquation25SoftReciprocalKernel_zero (lam : Real) :
    suzukiEquation25SoftReciprocalKernel lam 0 = -lam / 2 := by
  simp [suzukiEquation25SoftReciprocalKernel]
  ring

theorem suzukiEquation25SoftReciprocalKernel_neg (lam t : Real) :
    suzukiEquation25SoftReciprocalKernel lam (-t) =
      suzukiEquation25SoftReciprocalKernel lam t := by
  simp [suzukiEquation25SoftReciprocalKernel]

/-- Away from zero, the integral representation is the standard exponential
soft cutoff. -/
theorem suzukiEquation25SoftReciprocalKernel_eq_of_ne
    {lam t : Real} (ht : t ≠ 0) :
    suzukiEquation25SoftReciprocalKernel lam t =
      (Real.exp (-lam * |t|) - 1) / (2 * |t|) := by
  have habs : |t| ≠ 0 := abs_ne_zero.mpr ht
  have hderiv (s : Real) :
      HasDerivAt
        (fun r : Real => -Real.exp (-r * |t|) / |t|)
        (Real.exp (-s * |t|)) s := by
    have hlin : HasDerivAt (fun r : Real => -r * |t|) (-|t|) s := by
      simpa using (hasDerivAt_id s).neg.mul_const |t|
    have hraw :=
      ((Real.hasDerivAt_exp (-s * |t|)).comp s hlin).neg.div_const |t|
    have hclean : HasDerivAt
        (fun x : Real => (-Real.exp ∘ fun r : Real => -r * |t|) x / |t|)
        (Real.exp (-s * |t|)) s := by
      apply hraw.congr_deriv
      field_simp [habs]
    apply hclean.congr_of_eventuallyEq
    filter_upwards with r
    rfl
  have heval :
      (∫ s in (0 : Real)..lam, Real.exp (-s * |t|)) =
        (1 - Real.exp (-lam * |t|)) / |t| := by
    have hfund :
        (∫ s in (0 : Real)..lam, Real.exp (-s * |t|)) =
          (-Real.exp (-lam * |t|) / |t|) -
            (-Real.exp (-(0 : Real) * |t|) / |t|) := by
      apply intervalIntegral.integral_deriv_eq_sub'
        (f := fun s : Real => -Real.exp (-s * |t|) / |t|)
      · funext s
        exact (hderiv s).deriv
      · exact fun s _ => (hderiv s).differentiableAt
      · fun_prop
    rw [hfund]
    simp only [zero_mul, neg_zero, Real.exp_zero]
    field_simp [habs]
    ring
  rw [suzukiEquation25SoftReciprocalKernel, heval]
  field_simp [habs]
  ring

/-- For positive scale the removable quotient is bounded by its value at the
origin. -/
theorem norm_suzukiEquation25SoftReciprocalKernel_le
    {lam : Real} (hlam : 0 ≤ lam) (t : Real) :
    ‖suzukiEquation25SoftReciprocalKernel lam t‖ ≤ lam / 2 := by
  by_cases ht : t = 0
  · subst t
    simp [abs_of_nonneg hlam]
  · rw [suzukiEquation25SoftReciprocalKernel_eq_of_ne ht,
      Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_pos (by positivity : 0 < (2 : Real)), abs_abs]
    have hexpLe : Real.exp (-lam * |t|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have := abs_nonneg t
        nlinarith)
    have hdiff : 1 - Real.exp (-lam * |t|) ≤ lam * |t| := by
      linarith [Real.add_one_le_exp (-lam * |t|)]
    rw [abs_of_nonpos (sub_nonpos.mpr hexpLe)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * |t|)).2
    nlinarith

end

end M100
end Experiments
end RiemannHypothesisProject
