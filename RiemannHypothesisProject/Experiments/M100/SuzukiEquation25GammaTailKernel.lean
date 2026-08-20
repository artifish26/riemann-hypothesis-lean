import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25ShiftedHarmonicLimit
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointSmoothTransformIdentity

/-!
# Gamma tail kernel in Suzuki's equation (2.5)

This module packages the continuous remainder left after removing the first
`N` raw quarter-line exponentials from Suzuki's regularized `r1''` kernel.
Away from the origin it is the shifted geometric tail minus the reciprocal
singularity.  Its transition scale is therefore exactly `1 / N`.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open scoped BigOperators

/-- The first `N` raw quarter-line exponentials in the Gamma kernel. -/
def suzukiEquation25RawGammaExponentialPartial
    (N : Nat) (x : Real) : Real :=
  ∑ n ∈ Finset.range N, suzukiEquation25RawGammaExponentialKernel n x

/-- The continuous Gamma remainder after the first `N` raw exponentials have
been removed from the regularized `r1''` kernel. -/
def suzukiEquation25GammaTailKernel (N : Nat) (x : Real) : Real :=
  suzukiR1SecondKernel x -
    suzukiEquation25RawGammaExponentialPartial N x

theorem continuous_suzukiEquation25RawGammaExponentialKernel (n : Nat) :
    Continuous (suzukiEquation25RawGammaExponentialKernel n) := by
  unfold suzukiEquation25RawGammaExponentialKernel
  exact Real.continuous_exp.comp
    (continuous_const.mul continuous_abs)

theorem continuous_suzukiEquation25RawGammaExponentialPartial (N : Nat) :
    Continuous (suzukiEquation25RawGammaExponentialPartial N) := by
  unfold suzukiEquation25RawGammaExponentialPartial
  exact continuous_finsetSum _ fun n _ =>
    continuous_suzukiEquation25RawGammaExponentialKernel n

theorem continuous_suzukiEquation25GammaTailKernel (N : Nat) :
    Continuous (suzukiEquation25GammaTailKernel N) := by
  exact continuous_suzukiR1SecondKernel.sub
    (continuous_suzukiEquation25RawGammaExponentialPartial N)

@[simp]
theorem suzukiEquation25RawGammaExponentialKernel_zero (n : Nat) :
    suzukiEquation25RawGammaExponentialKernel n 0 = 1 := by
  simp [suzukiEquation25RawGammaExponentialKernel]

@[simp]
theorem suzukiEquation25RawGammaExponentialPartial_zero (N : Nat) :
    suzukiEquation25RawGammaExponentialPartial N 0 = N := by
  simp [suzukiEquation25RawGammaExponentialPartial]

@[simp]
theorem suzukiEquation25GammaTailKernel_zero (N : Nat) :
    suzukiEquation25GammaTailKernel N 0 = 1 / 4 - N := by
  simp [suzukiEquation25GammaTailKernel]

theorem suzukiEquation25RawGammaExponentialKernel_eq_restorationDecay
    (n : Nat) (x : Real) :
    suzukiEquation25RawGammaExponentialKernel n x =
      Real.exp (-suzukiDF6D4RestorationDecay n * |x|) := by
  unfold suzukiEquation25RawGammaExponentialKernel
    suzukiDF6D4RestorationDecay
  congr 1

/-- Removing a finite prefix from the full exponential series leaves the
shifted exponential tail. -/
theorem tsum_exp_neg_restorationDecay_mul_sub_partial
    {t : Real} (ht : 0 < t) (N : Nat) :
    (∑' n : Nat, Real.exp (-suzukiDF6D4RestorationDecay n * t)) -
        ∑ n ∈ Finset.range N,
          Real.exp (-suzukiDF6D4RestorationDecay n * t) =
      ∑' n : Nat,
        Real.exp (-suzukiDF6D4RestorationDecay (n + N) * t) := by
  have hsum := summable_exp_neg_restorationDecay_mul ht
  have hsplit := hsum.sum_add_tsum_nat_add N
  rw [← hsplit]
  ring

/-- The shifted exponential tail has the expected closed geometric form. -/
theorem tsum_exp_neg_restorationDecay_natAdd_mul
    {t : Real} (ht : 0 < t) (N : Nat) :
    (∑' n : Nat,
        Real.exp (-suzukiDF6D4RestorationDecay (n + N) * t)) =
      Real.exp (-(2 * (N : Real) + 1 / 2) * t) /
        (1 - Real.exp (-2 * t)) := by
  calc
    (∑' n : Nat,
        Real.exp (-suzukiDF6D4RestorationDecay (n + N) * t)) =
        ∑' n : Nat,
          Real.exp (-(2 * (N : Real)) * t) *
            Real.exp (-suzukiDF6D4RestorationDecay n * t) := by
          apply tsum_congr
          intro n
          rw [← Real.exp_add]
          unfold suzukiDF6D4RestorationDecay
          congr 1
          push_cast
          ring
    _ = Real.exp (-(2 * (N : Real)) * t) *
          (∑' n : Nat,
            Real.exp (-suzukiDF6D4RestorationDecay n * t)) := by
          rw [tsum_mul_left]
    _ = Real.exp (-(2 * (N : Real)) * t) *
          (Real.exp (-t / 2) / (1 - Real.exp (-2 * t))) := by
          rw [tsum_exp_neg_restorationDecay_mul ht]
    _ = Real.exp (-(2 * (N : Real) + 1 / 2) * t) /
          (1 - Real.exp (-2 * t)) := by
          rw [mul_div, ← Real.exp_add]
          congr 1
          ring

/-- Exact positive-half-line formula for the continuous Gamma tail. -/
theorem suzukiEquation25GammaTailKernel_eq_of_pos
    {t : Real} (ht : 0 < t) (N : Nat) :
    suzukiEquation25GammaTailKernel N t =
      Real.exp (-(2 * (N : Real) + 1 / 2) * t) /
          (1 - Real.exp (-2 * t)) -
        1 / (2 * t) := by
  rw [suzukiEquation25GammaTailKernel,
    suzukiR1SecondKernel_eq_tsum_sub_of_pos ht]
  unfold suzukiEquation25RawGammaExponentialPartial
  rw [Finset.sum_congr rfl (fun n _ =>
    suzukiEquation25RawGammaExponentialKernel_eq_restorationDecay n t)]
  rw [abs_of_pos ht]
  calc
    (∑' k : Nat, Real.exp (-suzukiDF6D4RestorationDecay k * t)) -
          1 / (2 * t) -
          ∑ n ∈ Finset.range N,
            Real.exp (-suzukiDF6D4RestorationDecay n * t) =
        ((∑' k : Nat,
            Real.exp (-suzukiDF6D4RestorationDecay k * t)) -
          ∑ n ∈ Finset.range N,
            Real.exp (-suzukiDF6D4RestorationDecay n * t)) -
          1 / (2 * t) := by ring
    _ = (∑' n : Nat,
          Real.exp (-suzukiDF6D4RestorationDecay (n + N) * t)) -
          1 / (2 * t) := by
          rw [tsum_exp_neg_restorationDecay_mul_sub_partial ht N]
    _ = Real.exp (-(2 * (N : Real) + 1 / 2) * t) /
          (1 - Real.exp (-2 * t)) -
        1 / (2 * t) := by
          rw [tsum_exp_neg_restorationDecay_natAdd_mul ht N]

end

end M100
end Experiments
end RiemannHypothesisProject
