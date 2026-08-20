import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualEnclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointResidualTailCoordinateExpansion
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointResidualTailMatrixAssembly

/-!
# Galerkin residual-tail expansion for M100-DF6D4

The frozen residual column is the complete low-to-tail column minus the
rational Galerkin approximant applied to the comparison band-to-tail column.
This module proves that the exact column splits into the five-term structured
prefix and the geometric remainder, for both parities and every tail mode from
601 onward.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators

def suzukiDF6D4EvenResidualTailPrefix
    (mode : Nat) (i : Fin 45) : Real :=
  suzukiDF6D4EvenTailPrefix suzukiDF6D4CompleteSineTransform
      (suzukiDF6D4EvenLowMode i) mode -
    ∑ k : Fin 256,
      (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
        suzukiDF6D4EvenTailPrefix suzukiDF6D4ComparisonSineTransform
          (suzukiDF6D4GalerkinMode k) mode

def suzukiDF6D4EvenResidualTailRemainder
    (mode : Nat) (i : Fin 45) : Real :=
  suzukiDF6D4EvenTailRemainder suzukiDF6D4CompleteSineTransform
      (suzukiDF6D4EvenLowMode i) mode -
    ∑ k : Fin 256,
      (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
        suzukiDF6D4EvenTailRemainder suzukiDF6D4ComparisonSineTransform
          (suzukiDF6D4GalerkinMode k) mode

def suzukiDF6D4OddResidualTailPrefix
    (mode : Nat) (i : Fin 44) : Real :=
  suzukiDF6D4OddTailPrefix suzukiDF6D4CompleteSineTransform
      (suzukiDF6D4OddLowMode i) mode -
    ∑ k : Fin 256,
      (suzukiDF6D4OddGalerkinApproximant k i : Real) *
        suzukiDF6D4OddTailPrefix suzukiDF6D4ComparisonSineTransform
          (suzukiDF6D4GalerkinMode k) mode

def suzukiDF6D4OddResidualTailRemainder
    (mode : Nat) (i : Fin 44) : Real :=
  suzukiDF6D4OddTailRemainder suzukiDF6D4CompleteSineTransform
      (suzukiDF6D4OddLowMode i) mode -
    ∑ k : Fin 256,
      (suzukiDF6D4OddGalerkinApproximant k i : Real) *
        suzukiDF6D4OddTailRemainder suzukiDF6D4ComparisonSineTransform
          (suzukiDF6D4GalerkinMode k) mode

theorem suzukiDF6D4EvenResidualColumn_eq_tailPrefix_add_remainder
    (mode : Nat) (hmode : 601 ≤ mode) (i : Fin 45) :
    suzukiDF6D4EvenResidualColumn mode i =
      suzukiDF6D4EvenResidualTailPrefix mode i +
        suzukiDF6D4EvenResidualTailRemainder mode i := by
  unfold suzukiDF6D4EvenResidualColumn
    suzukiDF6D4EvenResidualTailPrefix
    suzukiDF6D4EvenResidualTailRemainder
  have hlow : suzukiDF6D4EvenLowMode i < mode := by
    have := i.isLt
    simp only [suzukiDF6D4EvenLowMode]
    omega
  rw [suzukiDF6D4EvenOffDiagonal_eq_tailPrefix_add_remainder
    _ _ hlow]
  have hband : ∀ k : Fin 256, suzukiDF6D4GalerkinMode k < mode := by
    intro k
    have := k.isLt
    simp only [suzukiDF6D4GalerkinMode]
    omega
  simp_rw [suzukiDF6D4ComparisonEvenOffDiagonal_eq_tailPrefix_add_remainder
    _ _ (by simp [suzukiDF6D4GalerkinMode]) (hband _), mul_add]
  rw [Finset.sum_add_distrib]
  ring

theorem suzukiDF6D4OddResidualColumn_eq_tailPrefix_add_remainder
    (mode : Nat) (hmode : 601 ≤ mode) (i : Fin 44) :
    suzukiDF6D4OddResidualColumn mode i =
      suzukiDF6D4OddResidualTailPrefix mode i +
        suzukiDF6D4OddResidualTailRemainder mode i := by
  unfold suzukiDF6D4OddResidualColumn
    suzukiDF6D4OddResidualTailPrefix
    suzukiDF6D4OddResidualTailRemainder
  have hlowPos : 0 < suzukiDF6D4OddLowMode i := by
    simp [suzukiDF6D4OddLowMode]
  have hlow : suzukiDF6D4OddLowMode i < mode := by
    have := i.isLt
    simp only [suzukiDF6D4OddLowMode]
    omega
  rw [suzukiDF6D4OddOffDiagonal_eq_tailPrefix_add_remainder
    _ _ hlow]
  have hband : ∀ k : Fin 256, suzukiDF6D4GalerkinMode k < mode := by
    intro k
    have := k.isLt
    simp only [suzukiDF6D4GalerkinMode]
    omega
  simp_rw [suzukiDF6D4ComparisonOddOffDiagonal_eq_tailPrefix_add_remainder
    _ _ (by simp [suzukiDF6D4GalerkinMode]) (hband _), mul_add]
  rw [Finset.sum_add_distrib]
  ring

/-! ## Five structured Galerkin residual components -/

def suzukiDF6D4EvenResidualTailComponent
    (order mode : Nat) (i : Fin 45) : Real :=
  suzukiDF6D4EvenTailComponent suzukiDF6D4CompleteSineTransform order
      (suzukiDF6D4EvenLowMode i) mode -
    ∑ k : Fin 256,
      (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
        suzukiDF6D4EvenTailComponent suzukiDF6D4ComparisonSineTransform order
          (suzukiDF6D4GalerkinMode k) mode

def suzukiDF6D4OddResidualTailComponent
    (order mode : Nat) (i : Fin 44) : Real :=
  suzukiDF6D4OddTailComponent suzukiDF6D4CompleteSineTransform order
      (suzukiDF6D4OddLowMode i) mode -
    ∑ k : Fin 256,
      (suzukiDF6D4OddGalerkinApproximant k i : Real) *
        suzukiDF6D4OddTailComponent suzukiDF6D4ComparisonSineTransform order
          (suzukiDF6D4GalerkinMode k) mode

theorem suzukiDF6D4EvenResidualTailPrefix_eq_sum_components
    (mode : Nat) (i : Fin 45) :
    suzukiDF6D4EvenResidualTailPrefix mode i =
      ∑ order ∈ Finset.range 5,
        suzukiDF6D4EvenResidualTailComponent order mode i := by
  unfold suzukiDF6D4EvenResidualTailPrefix
    suzukiDF6D4EvenResidualTailComponent
  rw [suzukiDF6D4EvenTailPrefix_eq_sum_components]
  simp_rw [suzukiDF6D4EvenTailPrefix_eq_sum_components, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]

theorem suzukiDF6D4OddResidualTailPrefix_eq_sum_components
    (mode : Nat) (i : Fin 44) :
    suzukiDF6D4OddResidualTailPrefix mode i =
      ∑ order ∈ Finset.range 5,
        suzukiDF6D4OddResidualTailComponent order mode i := by
  unfold suzukiDF6D4OddResidualTailPrefix
    suzukiDF6D4OddResidualTailComponent
  rw [suzukiDF6D4OddTailPrefix_eq_sum_components]
  simp_rw [suzukiDF6D4OddTailPrefix_eq_sum_components, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]

/-! ## Exact residual moment vectors -/

def suzukiDF6D4EvenResidualTailTransformMoment
    (order : Nat) (i : Fin 45) : Real :=
  suzukiDF6D4EvenTailTransformMoment order (suzukiDF6D4EvenLowMode i) -
    ∑ k : Fin 256,
      (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
        suzukiDF6D4EvenTailTransformMoment order
          (suzukiDF6D4GalerkinMode k)

def suzukiDF6D4EvenResidualTailFixedMoment
    (order : Nat) (i : Fin 45) : Real :=
  suzukiDF6D4EvenTailFixedMoment suzukiDF6D4CompleteSineTransform order
      (suzukiDF6D4EvenLowMode i) -
    ∑ k : Fin 256,
      (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
        suzukiDF6D4EvenTailFixedMoment suzukiDF6D4ComparisonSineTransform order
          (suzukiDF6D4GalerkinMode k)

def suzukiDF6D4OddResidualTailTransformMoment
    (order : Nat) (i : Fin 44) : Real :=
  suzukiDF6D4OddTailTransformMoment order (suzukiDF6D4OddLowMode i) -
    ∑ k : Fin 256,
      (suzukiDF6D4OddGalerkinApproximant k i : Real) *
        suzukiDF6D4OddTailTransformMoment order
          (suzukiDF6D4GalerkinMode k)

def suzukiDF6D4OddResidualTailFixedMoment
    (order : Nat) (i : Fin 44) : Real :=
  suzukiDF6D4OddTailFixedMoment suzukiDF6D4CompleteSineTransform order
      (suzukiDF6D4OddLowMode i) -
    ∑ k : Fin 256,
      (suzukiDF6D4OddGalerkinApproximant k i : Real) *
        suzukiDF6D4OddTailFixedMoment suzukiDF6D4ComparisonSineTransform order
          (suzukiDF6D4GalerkinMode k)

/-- Exact three-piece moment decomposition of one even Galerkin residual
component.  The transform correction is subsequently split into its explicit
prime and smooth pieces. -/
theorem suzukiDF6D4EvenResidualTailComponent_eq_momentForm
    (order mode : Nat) (hmode : 601 ≤ mode) (i : Fin 45) :
    suzukiDF6D4EvenResidualTailComponent order mode i =
      (((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
        (suzukiDF6D4EvenResidualTailTransformMoment order i *
              suzukiDF6D4ComparisonSineTransform mode /
                (mode : Real) ^ (2 * order + 1) +
          suzukiDF6D4EvenTailTransformMoment order
                (suzukiDF6D4EvenLowMode i) *
              (suzukiDF6D4PrimeSineTransform mode +
                suzukiDF6D4SmoothTransformDifference mode) /
                (mode : Real) ^ (2 * order + 1) -
          suzukiDF6D4EvenResidualTailFixedMoment order i /
            (mode : Real) ^ (2 * order + 2)) := by
  have hlow : suzukiDF6D4EvenLowMode i ≤ mode := by
    have := i.isLt
    simp only [suzukiDF6D4EvenLowMode]
    omega
  have hband : ∀ k : Fin 256, suzukiDF6D4GalerkinMode k ≤ mode := by
    intro k
    have := k.isLt
    simp only [suzukiDF6D4GalerkinMode]
    omega
  have hmode0 : mode ≠ 0 := by omega
  have hcomplete : suzukiDF6D4CompleteSineTransform mode =
      suzukiDF6D4ComparisonSineTransform mode +
        (suzukiDF6D4PrimeSineTransform mode +
          suzukiDF6D4SmoothTransformDifference mode) := by
    have := suzukiDF6D4Complete_sub_comparison_eq mode
    linarith
  have hsumBilinear
      (weight first second : Fin 256 → Real) (common left right : Real) :
      (∑ k, weight k * (common * (first k * left - second k * right))) =
        common * ((∑ k, weight k * first k) * left -
          (∑ k, weight k * second k) * right) := by
    calc
      _ = ∑ k, common *
          ((weight k * first k) * left -
            (weight k * second k) * right) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = common * ∑ k,
          ((weight k * first k) * left -
            (weight k * second k) * right) := by
        rw [Finset.mul_sum]
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  unfold suzukiDF6D4EvenResidualTailComponent
    suzukiDF6D4EvenResidualTailTransformMoment
    suzukiDF6D4EvenResidualTailFixedMoment
  rw [suzukiDF6D4EvenTailComponent_eq_factoredMomentForm
    _ _ _ _ hlow hmode0]
  simp_rw [suzukiDF6D4EvenTailComponent_eq_factoredMomentForm
    _ _ _ _ (hband _) hmode0]
  have hgalerkinSum :
      (∑ k : Fin 256,
        (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
          ((((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
            (suzukiDF6D4EvenTailTransformMoment order
                    (suzukiDF6D4GalerkinMode k) *
                  suzukiDF6D4ComparisonSineTransform mode /
                    (mode : Real) ^ (2 * order + 1) -
              suzukiDF6D4EvenTailFixedMoment
                    suzukiDF6D4ComparisonSineTransform order
                    (suzukiDF6D4GalerkinMode k) /
                  (mode : Real) ^ (2 * order + 2)))) =
        (((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
          (((∑ k : Fin 256,
              (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
                suzukiDF6D4EvenTailTransformMoment order
                  (suzukiDF6D4GalerkinMode k)) *
                suzukiDF6D4ComparisonSineTransform mode /
                  (mode : Real) ^ (2 * order + 1)) -
            ((∑ k : Fin 256,
              (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
                suzukiDF6D4EvenTailFixedMoment
                  suzukiDF6D4ComparisonSineTransform order
                  (suzukiDF6D4GalerkinMode k)) /
                (mode : Real) ^ (2 * order + 2))) := by
    convert hsumBilinear
      (fun k => (suzukiDF6D4EvenGalerkinApproximant k i : Real))
      (fun k => suzukiDF6D4EvenTailTransformMoment order
        (suzukiDF6D4GalerkinMode k))
      (fun k => suzukiDF6D4EvenTailFixedMoment
        suzukiDF6D4ComparisonSineTransform order
        (suzukiDF6D4GalerkinMode k))
      ((((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹)
      (suzukiDF6D4ComparisonSineTransform mode /
        (mode : Real) ^ (2 * order + 1))
      (1 / (mode : Real) ^ (2 * order + 2)) using 1
    · apply Finset.sum_congr rfl
      intro k _
      ring
    · ring
  rw [hgalerkinSum]
  rw [hcomplete]
  ring

/-- Exact three-piece moment decomposition of one odd Galerkin residual
component. -/
theorem suzukiDF6D4OddResidualTailComponent_eq_momentForm
    (order mode : Nat) (hmode : 601 ≤ mode) (i : Fin 44) :
    suzukiDF6D4OddResidualTailComponent order mode i =
      (((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
        (suzukiDF6D4OddResidualTailTransformMoment order i *
              suzukiDF6D4ComparisonSineTransform mode /
                (mode : Real) ^ (2 * order + 2) +
          suzukiDF6D4OddTailTransformMoment order
                (suzukiDF6D4OddLowMode i) *
              (suzukiDF6D4PrimeSineTransform mode +
                suzukiDF6D4SmoothTransformDifference mode) /
                (mode : Real) ^ (2 * order + 2) -
          suzukiDF6D4OddResidualTailFixedMoment order i /
            (mode : Real) ^ (2 * order + 1)) := by
  have hlow : suzukiDF6D4OddLowMode i ≤ mode := by
    have := i.isLt
    simp only [suzukiDF6D4OddLowMode]
    omega
  have hband : ∀ k : Fin 256, suzukiDF6D4GalerkinMode k ≤ mode := by
    intro k
    have := k.isLt
    simp only [suzukiDF6D4GalerkinMode]
    omega
  have hmode0 : mode ≠ 0 := by omega
  have hcomplete : suzukiDF6D4CompleteSineTransform mode =
      suzukiDF6D4ComparisonSineTransform mode +
        (suzukiDF6D4PrimeSineTransform mode +
          suzukiDF6D4SmoothTransformDifference mode) := by
    have := suzukiDF6D4Complete_sub_comparison_eq mode
    linarith
  have hsumBilinear
      (weight first second : Fin 256 → Real) (common left right : Real) :
      (∑ k, weight k * (common * (first k * left - second k * right))) =
        common * ((∑ k, weight k * first k) * left -
          (∑ k, weight k * second k) * right) := by
    calc
      _ = ∑ k, common *
          ((weight k * first k) * left -
            (weight k * second k) * right) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = common * ∑ k,
          ((weight k * first k) * left -
            (weight k * second k) * right) := by
        rw [Finset.mul_sum]
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  unfold suzukiDF6D4OddResidualTailComponent
    suzukiDF6D4OddResidualTailTransformMoment
    suzukiDF6D4OddResidualTailFixedMoment
  rw [suzukiDF6D4OddTailComponent_eq_factoredMomentForm
    _ _ _ _ hlow hmode0]
  simp_rw [suzukiDF6D4OddTailComponent_eq_factoredMomentForm
    _ _ _ _ (hband _) hmode0]
  have hgalerkinSum :
      (∑ k : Fin 256,
        (suzukiDF6D4OddGalerkinApproximant k i : Real) *
          ((((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
            (suzukiDF6D4OddTailTransformMoment order
                    (suzukiDF6D4GalerkinMode k) *
                  suzukiDF6D4ComparisonSineTransform mode /
                    (mode : Real) ^ (2 * order + 2) -
              suzukiDF6D4OddTailFixedMoment
                    suzukiDF6D4ComparisonSineTransform order
                    (suzukiDF6D4GalerkinMode k) /
                  (mode : Real) ^ (2 * order + 1)))) =
        (((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
          (((∑ k : Fin 256,
              (suzukiDF6D4OddGalerkinApproximant k i : Real) *
                suzukiDF6D4OddTailTransformMoment order
                  (suzukiDF6D4GalerkinMode k)) *
                suzukiDF6D4ComparisonSineTransform mode /
                  (mode : Real) ^ (2 * order + 2)) -
            ((∑ k : Fin 256,
              (suzukiDF6D4OddGalerkinApproximant k i : Real) *
                suzukiDF6D4OddTailFixedMoment
                  suzukiDF6D4ComparisonSineTransform order
                  (suzukiDF6D4GalerkinMode k)) /
                (mode : Real) ^ (2 * order + 1))) := by
    convert hsumBilinear
      (fun k => (suzukiDF6D4OddGalerkinApproximant k i : Real))
      (fun k => suzukiDF6D4OddTailTransformMoment order
        (suzukiDF6D4GalerkinMode k))
      (fun k => suzukiDF6D4OddTailFixedMoment
        suzukiDF6D4ComparisonSineTransform order
        (suzukiDF6D4GalerkinMode k))
      ((((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹)
      (suzukiDF6D4ComparisonSineTransform mode /
        (mode : Real) ^ (2 * order + 2))
      (1 / (mode : Real) ^ (2 * order + 1)) using 1
    · apply Finset.sum_congr rfl
      intro k _
      ring
    · ring
  rw [hgalerkinSum]
  rw [hcomplete]
  ring

/-! ## Sharp order-zero splits -/

/-- The even leading tail retains the constant comparison-transform term and
the explicit prime oscillation.  These two terms are summed sharply rather
than bounded by an absolute inverse-square tail. -/
def suzukiDF6D4EvenResidualTailMain
    (mode : Nat) (i : Fin 45) : Real :=
  (((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
    (-(Real.pi / 2) * suzukiDF6D4EvenResidualTailTransformMoment 0 i /
          (mode : Real) +
      suzukiDF6D4EvenTailTransformMoment 0 (suzukiDF6D4EvenLowMode i) *
          suzukiDF6D4PrimeSineTransform mode / (mode : Real))

/-- The remaining even order-zero terms all acquire a second inverse power:
the comparison sine tail and smooth transform are each `O(n⁻¹)`, while the
fixed moment already carries `n⁻²`. -/
def suzukiDF6D4EvenResidualTailOrderZeroRemainder
    (mode : Nat) (i : Fin 45) : Real :=
  (((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
    (suzukiDF6D4EvenResidualTailTransformMoment 0 i *
          suzukiDF6D4ComparisonSineTail mode / (mode : Real) +
      suzukiDF6D4EvenTailTransformMoment 0 (suzukiDF6D4EvenLowMode i) *
          suzukiDF6D4SmoothTransformDifference mode / (mode : Real) -
      suzukiDF6D4EvenResidualTailFixedMoment 0 i / (mode : Real) ^ 2)

theorem suzukiDF6D4EvenResidualTailComponent_zero_eq_main_add_remainder
    (mode : Nat) (hmode : 601 ≤ mode) (i : Fin 45) :
    suzukiDF6D4EvenResidualTailComponent 0 mode i =
      suzukiDF6D4EvenResidualTailMain mode i +
        suzukiDF6D4EvenResidualTailOrderZeroRemainder mode i := by
  rw [suzukiDF6D4EvenResidualTailComponent_eq_momentForm 0 mode hmode i]
  unfold suzukiDF6D4EvenResidualTailMain
    suzukiDF6D4EvenResidualTailOrderZeroRemainder
    suzukiDF6D4ComparisonSineTransform
    suzukiDF6D4ComparisonSineIntegral
  norm_num
  ring

/-- The odd leading tail is the fixed order-zero residual vector divided by
the tail mode. -/
def suzukiDF6D4OddResidualTailMain
    (mode : Nat) (i : Fin 44) : Real :=
  (((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
    (-suzukiDF6D4OddResidualTailFixedMoment 0 i / (mode : Real))

/-- The two remaining odd order-zero transform terms carry `n⁻²`. -/
def suzukiDF6D4OddResidualTailOrderZeroRemainder
    (mode : Nat) (i : Fin 44) : Real :=
  (((suzukiDF6D4TailParity mode : Rat) : Real)) * Real.pi⁻¹ *
    (suzukiDF6D4OddResidualTailTransformMoment 0 i *
          suzukiDF6D4ComparisonSineTransform mode / (mode : Real) ^ 2 +
      suzukiDF6D4OddTailTransformMoment 0 (suzukiDF6D4OddLowMode i) *
          (suzukiDF6D4PrimeSineTransform mode +
            suzukiDF6D4SmoothTransformDifference mode) / (mode : Real) ^ 2)

theorem suzukiDF6D4OddResidualTailComponent_zero_eq_main_add_remainder
    (mode : Nat) (hmode : 601 ≤ mode) (i : Fin 44) :
    suzukiDF6D4OddResidualTailComponent 0 mode i =
      suzukiDF6D4OddResidualTailMain mode i +
        suzukiDF6D4OddResidualTailOrderZeroRemainder mode i := by
  rw [suzukiDF6D4OddResidualTailComponent_eq_momentForm 0 mode hmode i]
  unfold suzukiDF6D4OddResidualTailMain
    suzukiDF6D4OddResidualTailOrderZeroRemainder
  norm_num
  ring

/-! ## Concrete order-`n^-11` residual envelopes -/

def suzukiDF6D4EvenResidualGeometricEnvelope (i : Fin 45) : Real :=
  suzukiDF6D4EvenGeometricEnvelope suzukiDF6D4CompleteSineTransform
      (suzukiDF6D4EvenLowMode i) suzukiDF6D4CompleteTailTransformBound +
    ∑ k : Fin 256,
      |((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real)| *
        suzukiDF6D4EvenGeometricEnvelope suzukiDF6D4ComparisonSineTransform
          (suzukiDF6D4GalerkinMode k)
          suzukiDF6D4ComparisonTailTransformBound

def suzukiDF6D4OddResidualGeometricEnvelope (i : Fin 44) : Real :=
  suzukiDF6D4OddGeometricEnvelope suzukiDF6D4CompleteSineTransform
      (suzukiDF6D4OddLowMode i) suzukiDF6D4CompleteTailTransformBound +
    ∑ k : Fin 256,
      |((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real)| *
        suzukiDF6D4OddGeometricEnvelope suzukiDF6D4ComparisonSineTransform
          (suzukiDF6D4GalerkinMode k)
          suzukiDF6D4ComparisonTailTransformBound

theorem suzukiDF6D4EvenResidualGeometricEnvelope_nonneg (i : Fin 45) :
    0 ≤ suzukiDF6D4EvenResidualGeometricEnvelope i := by
  unfold suzukiDF6D4EvenResidualGeometricEnvelope
  exact add_nonneg
    (suzukiDF6D4EvenGeometricEnvelope_nonneg _ _ _
      (by simp [suzukiDF6D4EvenLowMode]; omega)
      suzukiDF6D4CompleteTailTransformBound_nonneg)
    (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _)
      (suzukiDF6D4EvenGeometricEnvelope_nonneg _ _ _
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        suzukiDF6D4ComparisonTailTransformBound_nonneg))

theorem suzukiDF6D4OddResidualGeometricEnvelope_nonneg (i : Fin 44) :
    0 ≤ suzukiDF6D4OddResidualGeometricEnvelope i := by
  unfold suzukiDF6D4OddResidualGeometricEnvelope
  exact add_nonneg
    (suzukiDF6D4OddGeometricEnvelope_nonneg _ _ _
      (by simp [suzukiDF6D4OddLowMode]; omega)
      suzukiDF6D4CompleteTailTransformBound_nonneg)
    (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _)
      (suzukiDF6D4OddGeometricEnvelope_nonneg _ _ _
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        suzukiDF6D4ComparisonTailTransformBound_nonneg))

theorem suzukiDF6D4EvenResidualTailRemainder_abs_le
    (mode : Nat) (hmode : 601 ≤ mode) (i : Fin 45) :
    |suzukiDF6D4EvenResidualTailRemainder mode i| ≤
      suzukiDF6D4EvenResidualGeometricEnvelope i / (mode : Real) ^ 11 := by
  have hlow := suzukiDF6D4EvenTailRemainder_abs_le_orderEleven
    suzukiDF6D4CompleteSineTransform (suzukiDF6D4EvenLowMode i) mode
    suzukiDF6D4CompleteTailTransformBound
    (by simp [suzukiDF6D4EvenLowMode]; omega) hmode
    suzukiDF6D4CompleteTailTransformBound_nonneg
    (suzukiDF6D4CompleteSineTransform_abs_le_tailBound mode hmode)
  have hband : ∀ k : Fin 256,
      |suzukiDF6D4EvenTailRemainder suzukiDF6D4ComparisonSineTransform
          (suzukiDF6D4GalerkinMode k) mode| ≤
        suzukiDF6D4EvenGeometricEnvelope suzukiDF6D4ComparisonSineTransform
          (suzukiDF6D4GalerkinMode k)
          suzukiDF6D4ComparisonTailTransformBound / (mode : Real) ^ 11 := by
    intro k
    exact suzukiDF6D4EvenTailRemainder_abs_le_orderEleven
      suzukiDF6D4ComparisonSineTransform (suzukiDF6D4GalerkinMode k) mode
      suzukiDF6D4ComparisonTailTransformBound
      (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega) hmode
      suzukiDF6D4ComparisonTailTransformBound_nonneg
      (suzukiDF6D4ComparisonSineTransform_abs_le_frozen mode hmode)
  have hsum :
      |∑ k : Fin 256,
          (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
            suzukiDF6D4EvenTailRemainder suzukiDF6D4ComparisonSineTransform
              (suzukiDF6D4GalerkinMode k) mode| ≤
        ∑ k : Fin 256,
          |((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real)| *
            (suzukiDF6D4EvenGeometricEnvelope
              suzukiDF6D4ComparisonSineTransform
              (suzukiDF6D4GalerkinMode k)
              suzukiDF6D4ComparisonTailTransformBound / (mode : Real) ^ 11) := by
    calc
      |∑ k : Fin 256,
          (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
            suzukiDF6D4EvenTailRemainder suzukiDF6D4ComparisonSineTransform
              (suzukiDF6D4GalerkinMode k) mode| ≤
          ∑ k : Fin 256,
            |(suzukiDF6D4EvenGalerkinApproximant k i : Real) *
              suzukiDF6D4EvenTailRemainder suzukiDF6D4ComparisonSineTransform
                (suzukiDF6D4GalerkinMode k) mode| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hband k) (abs_nonneg _)
  have hsumDiv :
      (∑ k : Fin 256,
        |((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real)| *
          (suzukiDF6D4EvenGeometricEnvelope
            suzukiDF6D4ComparisonSineTransform
            (suzukiDF6D4GalerkinMode k)
            suzukiDF6D4ComparisonTailTransformBound / (mode : Real) ^ 11)) =
        (∑ k : Fin 256,
          |((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real)| *
            suzukiDF6D4EvenGeometricEnvelope
              suzukiDF6D4ComparisonSineTransform
              (suzukiDF6D4GalerkinMode k)
              suzukiDF6D4ComparisonTailTransformBound) / (mode : Real) ^ 11 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold suzukiDF6D4EvenResidualTailRemainder
    suzukiDF6D4EvenResidualGeometricEnvelope
  calc
    |_ - _| ≤ _ + _ := abs_sub _ _
    _ ≤ _ := add_le_add hlow hsum
    _ = _ := by rw [hsumDiv]; ring

theorem suzukiDF6D4OddResidualTailRemainder_abs_le
    (mode : Nat) (hmode : 601 ≤ mode) (i : Fin 44) :
    |suzukiDF6D4OddResidualTailRemainder mode i| ≤
      suzukiDF6D4OddResidualGeometricEnvelope i / (mode : Real) ^ 11 := by
  have hlow := suzukiDF6D4OddTailRemainder_abs_le_orderEleven
    suzukiDF6D4CompleteSineTransform (suzukiDF6D4OddLowMode i) mode
    suzukiDF6D4CompleteTailTransformBound
    (by simp [suzukiDF6D4OddLowMode]; omega) hmode
    suzukiDF6D4CompleteTailTransformBound_nonneg
    (suzukiDF6D4CompleteSineTransform_abs_le_tailBound mode hmode)
  have hband : ∀ k : Fin 256,
      |suzukiDF6D4OddTailRemainder suzukiDF6D4ComparisonSineTransform
          (suzukiDF6D4GalerkinMode k) mode| ≤
        suzukiDF6D4OddGeometricEnvelope suzukiDF6D4ComparisonSineTransform
          (suzukiDF6D4GalerkinMode k)
          suzukiDF6D4ComparisonTailTransformBound / (mode : Real) ^ 11 := by
    intro k
    exact suzukiDF6D4OddTailRemainder_abs_le_orderEleven
      suzukiDF6D4ComparisonSineTransform (suzukiDF6D4GalerkinMode k) mode
      suzukiDF6D4ComparisonTailTransformBound
      (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega) hmode
      suzukiDF6D4ComparisonTailTransformBound_nonneg
      (suzukiDF6D4ComparisonSineTransform_abs_le_frozen mode hmode)
  have hsum :
      |∑ k : Fin 256,
          (suzukiDF6D4OddGalerkinApproximant k i : Real) *
            suzukiDF6D4OddTailRemainder suzukiDF6D4ComparisonSineTransform
              (suzukiDF6D4GalerkinMode k) mode| ≤
        ∑ k : Fin 256,
          |((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real)| *
            (suzukiDF6D4OddGeometricEnvelope
              suzukiDF6D4ComparisonSineTransform
              (suzukiDF6D4GalerkinMode k)
              suzukiDF6D4ComparisonTailTransformBound / (mode : Real) ^ 11) := by
    calc
      |∑ k : Fin 256,
          (suzukiDF6D4OddGalerkinApproximant k i : Real) *
            suzukiDF6D4OddTailRemainder suzukiDF6D4ComparisonSineTransform
              (suzukiDF6D4GalerkinMode k) mode| ≤
          ∑ k : Fin 256,
            |(suzukiDF6D4OddGalerkinApproximant k i : Real) *
              suzukiDF6D4OddTailRemainder suzukiDF6D4ComparisonSineTransform
                (suzukiDF6D4GalerkinMode k) mode| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hband k) (abs_nonneg _)
  have hsumDiv :
      (∑ k : Fin 256,
        |((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real)| *
          (suzukiDF6D4OddGeometricEnvelope
            suzukiDF6D4ComparisonSineTransform
            (suzukiDF6D4GalerkinMode k)
            suzukiDF6D4ComparisonTailTransformBound / (mode : Real) ^ 11)) =
        (∑ k : Fin 256,
          |((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real)| *
            suzukiDF6D4OddGeometricEnvelope
              suzukiDF6D4ComparisonSineTransform
              (suzukiDF6D4GalerkinMode k)
              suzukiDF6D4ComparisonTailTransformBound) / (mode : Real) ^ 11 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold suzukiDF6D4OddResidualTailRemainder
    suzukiDF6D4OddResidualGeometricEnvelope
  calc
    |_ - _| ≤ _ + _ := abs_sub _ _
    _ ≤ _ := add_le_add hlow hsum
    _ = _ := by rw [hsumDiv]; ring

/-! ## Geometric remainder Gram bounds -/

theorem suzukiDF6D4EvenResidualGeometricTailQuadratic_le
    (x : Fin 45 → Real) :
    (∑' k : Nat,
      (∑ i : Fin 45, x i *
        suzukiDF6D4EvenResidualTailRemainder (601 + k) i) ^ 2) ≤
      (∑ i : Fin 45, suzukiDF6D4EvenResidualGeometricEnvelope i) *
          (1 / (21 * (600 : Real) ^ 21)) *
        ∑ i : Fin 45,
          suzukiDF6D4EvenResidualGeometricEnvelope i * (x i) ^ 2 := by
  apply suzukiDF6D4FrozenOrderElevenTailQuadratic_le
  · exact suzukiDF6D4EvenResidualGeometricEnvelope_nonneg
  · intro k i
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      suzukiDF6D4EvenResidualTailRemainder_abs_le
        (601 + k) (by omega) i

theorem suzukiDF6D4OddResidualGeometricTailQuadratic_le
    (x : Fin 44 → Real) :
    (∑' k : Nat,
      (∑ i : Fin 44, x i *
        suzukiDF6D4OddResidualTailRemainder (601 + k) i) ^ 2) ≤
      (∑ i : Fin 44, suzukiDF6D4OddResidualGeometricEnvelope i) *
          (1 / (21 * (600 : Real) ^ 21)) *
        ∑ i : Fin 44,
          suzukiDF6D4OddResidualGeometricEnvelope i * (x i) ^ 2 := by
  apply suzukiDF6D4FrozenOrderElevenTailQuadratic_le
  · exact suzukiDF6D4OddResidualGeometricEnvelope_nonneg
  · intro k i
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      suzukiDF6D4OddResidualTailRemainder_abs_le
        (601 + k) (by omega) i

end

end RiemannHypothesisProject.Experiments.M100
