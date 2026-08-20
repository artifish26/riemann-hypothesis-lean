import RiemannHypothesisProject.Experiments.M100.SuzukiLogRadiusScalarParity
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# M100-B2 finite Yoshida projection geometry

This module isolates the finite-dimensional Hilbert-space part of the B2
Yoshida projection gate.  Given any finite orthonormal family in the ambient
global `L²` space, it constructs the bounded complex coordinate map, the
finite reconstruction, and the complementary far remainder.  It proves the
exact finite Parseval identity without any infinite-basis completeness
assumption.

The concrete endpoint cosine/sine modes and their membership in the
logarithmic radius completion are a separate analytic bridge.  Keeping that
bridge out of this file makes the projection geometry reusable and prevents a
boundary-density obligation from being hidden in the finite-dimensional
argument.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open scoped BigOperators ENNReal InnerProductSpace

variable {ι : Type*} [Fintype ι]

/-- Complex coordinates against a finite family in the ambient global `L²`
space.  The codomain is the Hilbert `ℓ²` structure on the finite coordinate
space. -/
def suzukiFiniteL2CoordinateMap (mode : ι → SuzukiL2) :
    SuzukiL2 →L[Complex] EuclideanSpace Complex ι :=
  (EuclideanSpace.equiv ι Complex).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => innerSL Complex (mode i))

omit [Fintype ι] in
@[simp]
theorem suzukiFiniteL2CoordinateMap_apply
    (mode : ι → SuzukiL2) (v : SuzukiL2) (i : ι) :
    suzukiFiniteL2CoordinateMap mode v i =
      inner Complex (mode i) v := by
  rfl

/-- Reconstruction from a finite complex coordinate vector. -/
def suzukiFiniteL2Reconstruction (mode : ι → SuzukiL2) :
    EuclideanSpace Complex ι →L[Complex] SuzukiL2 :=
  ∑ i, (EuclideanSpace.proj i).smulRight (mode i)

@[simp]
theorem suzukiFiniteL2Reconstruction_apply
    (mode : ι → SuzukiL2) (x : EuclideanSpace Complex ι) :
    suzukiFiniteL2Reconstruction mode x =
      ∑ i, x i • mode i := by
  simp [suzukiFiniteL2Reconstruction]

/-- Finite orthogonal-projection formula associated with a family of modes.
It is an actual orthogonal projection when the family is orthonormal. -/
def suzukiFiniteL2LowProjection (mode : ι → SuzukiL2) :
    SuzukiL2 →L[Complex] SuzukiL2 :=
  (suzukiFiniteL2Reconstruction mode).comp
    (suzukiFiniteL2CoordinateMap mode)

@[simp]
theorem suzukiFiniteL2LowProjection_apply
    (mode : ι → SuzukiL2) (v : SuzukiL2) :
    suzukiFiniteL2LowProjection mode v =
      ∑ i, inner Complex (mode i) v • mode i := by
  simp [suzukiFiniteL2LowProjection]

/-- The complementary far remainder after removing the finite low-mode
reconstruction. -/
def suzukiFiniteL2FarRemainder (mode : ι → SuzukiL2) :
    SuzukiL2 →L[Complex] SuzukiL2 :=
  ContinuousLinearMap.id Complex SuzukiL2 -
    suzukiFiniteL2LowProjection mode

@[simp]
theorem suzukiFiniteL2FarRemainder_apply
    (mode : ι → SuzukiL2) (v : SuzukiL2) :
    suzukiFiniteL2FarRemainder mode v =
      v - ∑ i, inner Complex (mode i) v • mode i := by
  simp [suzukiFiniteL2FarRemainder]

theorem suzukiFiniteL2LowProjection_add_farRemainder
    (mode : ι → SuzukiL2) (v : SuzukiL2) :
    suzukiFiniteL2LowProjection mode v +
      suzukiFiniteL2FarRemainder mode v = v := by
  simp [suzukiFiniteL2FarRemainder]

/-- Every retained mode is orthogonal to the far remainder. -/
theorem inner_suzukiFiniteL2Mode_farRemainder
    {mode : ι → SuzukiL2} (hmode : Orthonormal Complex mode)
    (v : SuzukiL2) (i : ι) :
    inner Complex (mode i) (suzukiFiniteL2FarRemainder mode v) = 0 := by
  rw [suzukiFiniteL2FarRemainder_apply, inner_sub_right,
    hmode.inner_right_fintype]
  simp

/-- The low reconstruction is orthogonal to the far remainder. -/
theorem inner_suzukiFiniteL2LowProjection_farRemainder
    {mode : ι → SuzukiL2} (hmode : Orthonormal Complex mode)
    (v : SuzukiL2) :
    inner Complex (suzukiFiniteL2LowProjection mode v)
      (suzukiFiniteL2FarRemainder mode v) = 0 := by
  rw [suzukiFiniteL2LowProjection_apply, sum_inner]
  apply Finset.sum_eq_zero
  intro i hi
  rw [inner_smul_left,
    inner_suzukiFiniteL2Mode_farRemainder hmode v i]
  simp

/-- The squared norm of the low reconstruction is the sum of squared
coordinate norms. -/
theorem suzukiFiniteL2LowProjection_norm_sq
    {mode : ι → SuzukiL2} (hmode : Orthonormal Complex mode)
    (v : SuzukiL2) :
    ‖suzukiFiniteL2LowProjection mode v‖ ^ 2 =
      ∑ i, ‖inner Complex (mode i) v‖ ^ 2 := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner Complex SuzukiL2,
    suzukiFiniteL2LowProjection_apply,
    hmode.inner_sum (fun i => inner Complex (mode i) v)
      (fun i => inner Complex (mode i) v) Finset.univ]
  rw [map_sum]
  simp_rw [Complex.conj_mul']
  apply Finset.sum_congr rfl
  intro i hi
  norm_cast

/-- Exact finite Parseval identity: total ambient `L²` mass is the retained
coordinate mass plus the complementary far mass. -/
theorem suzukiFiniteL2_parseval
    {mode : ι → SuzukiL2} (hmode : Orthonormal Complex mode)
    (v : SuzukiL2) :
    ‖v‖ ^ 2 =
      (∑ i, ‖suzukiFiniteL2CoordinateMap mode v i‖ ^ 2) +
        ‖suzukiFiniteL2FarRemainder mode v‖ ^ 2 := by
  calc
    ‖v‖ ^ 2 =
        ‖suzukiFiniteL2LowProjection mode v +
          suzukiFiniteL2FarRemainder mode v‖ ^ 2 := by
      rw [suzukiFiniteL2LowProjection_add_farRemainder]
    _ = ‖suzukiFiniteL2LowProjection mode v‖ ^ 2 +
          ‖suzukiFiniteL2FarRemainder mode v‖ ^ 2 := by
      simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          _ _ (inner_suzukiFiniteL2LowProjection_farRemainder hmode v)
    _ = (∑ i, ‖suzukiFiniteL2CoordinateMap mode v i‖ ^ 2) +
          ‖suzukiFiniteL2FarRemainder mode v‖ ^ 2 := by
      rw [suzukiFiniteL2LowProjection_norm_sq hmode]
      rfl

/-! ## Radius-completion receiving surface -/

/-- The exact finite-mode data required from the analytic Yoshida-mode
membership bridge.  Membership in the radius completion is visible in the
types; ambient `L²` orthonormality and parity are visible as separate fields.

This record is intentionally narrow.  It does not bundle endpoint form
identities or positivity assumptions. -/
structure SuzukiB2EndpointModeCertificate (r : Real) where
  evenMode : Fin 45 → SuzukiLogRadiusLinearCompletion r
  oddMode : Fin 44 → SuzukiLogRadiusLinearCompletion r
  evenOrthonormal :
    Orthonormal Complex
      (fun i => suzukiLogRadiusLinearCompletionToL2 (evenMode i))
  oddOrthonormal :
    Orthonormal Complex
      (fun i => suzukiLogRadiusLinearCompletionToL2 (oddMode i))
  evenParity :
    ∀ i, SuzukiL2Even
      (suzukiLogRadiusLinearCompletionToL2 (evenMode i))
  oddParity :
    ∀ i, SuzukiL2Odd
      (suzukiLogRadiusLinearCompletionToL2 (oddMode i))

/-- The bounded 45-dimensional even low-coordinate map on the radius
completion. -/
def SuzukiB2EndpointModeCertificate.evenCoordinateMap
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    SuzukiLogRadiusLinearCompletion r →L[Complex]
      EuclideanSpace Complex (Fin 45) :=
  (suzukiFiniteL2CoordinateMap
      (fun i => suzukiLogRadiusLinearCompletionToL2
        (certificate.evenMode i))).comp
    suzukiLogRadiusLinearCompletionToL2

@[simp]
theorem SuzukiB2EndpointModeCertificate.evenCoordinateMap_apply
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) (i : Fin 45) :
    certificate.evenCoordinateMap v i =
      inner Complex
        (suzukiLogRadiusLinearCompletionToL2
          (certificate.evenMode i))
        (suzukiLogRadiusLinearCompletionToL2 v) := by
  rfl

/-- The bounded 44-dimensional odd low-coordinate map on the radius
completion. -/
def SuzukiB2EndpointModeCertificate.oddCoordinateMap
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    SuzukiLogRadiusLinearCompletion r →L[Complex]
      EuclideanSpace Complex (Fin 44) :=
  (suzukiFiniteL2CoordinateMap
      (fun i => suzukiLogRadiusLinearCompletionToL2
        (certificate.oddMode i))).comp
    suzukiLogRadiusLinearCompletionToL2

@[simp]
theorem SuzukiB2EndpointModeCertificate.oddCoordinateMap_apply
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) (i : Fin 44) :
    certificate.oddCoordinateMap v i =
      inner Complex
        (suzukiLogRadiusLinearCompletionToL2
          (certificate.oddMode i))
        (suzukiLogRadiusLinearCompletionToL2 v) := by
  rfl

/-- The even ambient-`L²` far remainder after removing modes `0, ..., 44`. -/
def SuzukiB2EndpointModeCertificate.evenFarRemainder
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    SuzukiLogRadiusLinearCompletion r →L[Complex] SuzukiL2 :=
  (suzukiFiniteL2FarRemainder
      (fun i => suzukiLogRadiusLinearCompletionToL2
        (certificate.evenMode i))).comp
    suzukiLogRadiusLinearCompletionToL2

/-- The odd ambient-`L²` far remainder after removing modes `1, ..., 44`. -/
def SuzukiB2EndpointModeCertificate.oddFarRemainder
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    SuzukiLogRadiusLinearCompletion r →L[Complex] SuzukiL2 :=
  (suzukiFiniteL2FarRemainder
      (fun i => suzukiLogRadiusLinearCompletionToL2
        (certificate.oddMode i))).comp
    suzukiLogRadiusLinearCompletionToL2

/-- Exact even-sector finite Parseval identity in the ambient `L²` norm. -/
theorem SuzukiB2EndpointModeCertificate.even_parseval
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    ‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 =
      (∑ i, ‖certificate.evenCoordinateMap v i‖ ^ 2) +
        ‖certificate.evenFarRemainder v‖ ^ 2 := by
  exact suzukiFiniteL2_parseval certificate.evenOrthonormal
    (suzukiLogRadiusLinearCompletionToL2 v)

/-- Exact odd-sector finite Parseval identity in the ambient `L²` norm. -/
theorem SuzukiB2EndpointModeCertificate.odd_parseval
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    ‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 =
      (∑ i, ‖certificate.oddCoordinateMap v i‖ ^ 2) +
        ‖certificate.oddFarRemainder v‖ ^ 2 := by
  exact suzukiFiniteL2_parseval certificate.oddOrthonormal
    (suzukiLogRadiusLinearCompletionToL2 v)

/-! ## Frozen B2 cutoff conventions -/

/-- The even B2 low block has physical Yoshida modes `0, ..., 44`. -/
def suzukiB2EvenLowPhysicalMode (i : Fin 45) : Nat := i

/-- The odd B2 low block has physical Yoshida modes `1, ..., 44`. -/
def suzukiB2OddLowPhysicalMode (i : Fin 44) : Nat := i + 1

@[simp]
theorem suzukiB2EvenLowPhysicalMode_lt_farStart (i : Fin 45) :
    suzukiB2EvenLowPhysicalMode i < 45 :=
  i.isLt

@[simp]
theorem suzukiB2OddLowPhysicalMode_pos (i : Fin 44) :
    0 < suzukiB2OddLowPhysicalMode i := by
  unfold suzukiB2OddLowPhysicalMode
  omega

@[simp]
theorem suzukiB2OddLowPhysicalMode_lt_farStart (i : Fin 44) :
    suzukiB2OddLowPhysicalMode i < 45 := by
  unfold suzukiB2OddLowPhysicalMode
  omega

/-- In both parity sectors the complementary physical-mode tail begins at
mode `45`. -/
def suzukiB2FarPhysicalModeStart : Nat := 45

end

end M100
end Experiments
end RiemannHypothesisProject
