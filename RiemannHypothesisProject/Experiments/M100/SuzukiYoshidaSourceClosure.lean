import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointModes

/-!
# M100-B2S Suzuki/Yoshida source closure

This module freezes the exact source theorem used at B2S and performs the
project-side normalization and finite-mode assembly.

Suzuki's Fourier transform is

`f_hat(z) = integral f(x) * exp (I * z * x) dx`,

whereas Mathlib's `FourierTransform.fourier` uses the `2 * pi` character.
Thus the source frequency is `z = -2 * pi * xi`.  Section 3.2 of Suzuki,
*Weil's quadratic form via the screw function* (arXiv:2606.09096v1), proves
that every periodic interval exponential

`x |-> exp (I * pi * n * x / r)`

is a form-norm limit of smooth functions compactly supported in `(-r,r)`.
The proof uses shrinking boundary cutoffs and the estimate
`O(epsilon * log (1 / epsilon))`.

`SuzukiYoshidaExponentialFormCoreSourceAt` records precisely that conclusion
after the Fourier change of variables: the approximants are the live
`SuzukiSmoothCore`, and convergence is in the live logarithmic multiplier
graph.  It is intentionally narrower than a characterization of every
supported logarithmic-domain element.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Filter Set
open scoped ENNReal Topology

/-- Bundle an endpoint exponential with its logarithmically weighted Fourier
coordinate as an element of the live closed multiplier graph. -/
def suzukiYoshidaExponentialLogGraph
    {r : Real} (hr : 0 < r) (n : Int)
    (hDomain :
      SuzukiLogFourierDomain (suzukiYoshidaExponentialL2 r hr n)) :
    SuzukiLogGraphSpace :=
  ⟨(suzukiYoshidaExponentialL2 r hr n,
      suzukiLogWeightedFourierToL2
        ⟨suzukiYoshidaExponentialL2 r hr n, hDomain⟩), by
    change
      (suzukiYoshidaExponentialL2 r hr n,
        suzukiLogWeightedFourierToL2
          ⟨suzukiYoshidaExponentialL2 r hr n, hDomain⟩) ∈
        suzukiLogFourierPMap.graph
    rw [LinearPMap.mem_graph_iff]
    exact
      ⟨⟨suzukiYoshidaExponentialL2 r hr n,
          (show suzukiYoshidaExponentialL2 r hr n ∈
              SuzukiLogFourierSubmodule by
            exact hDomain)⟩,
        rfl, rfl⟩⟩

/-- The exact literature-shaped B2S source theorem after converting
Suzuki's frequency variable `z` to Mathlib's Fourier variable.

The conclusion is sequence-level form-core approximation for the periodic
exponentials themselves.  It is not a general density hypothesis and does
not mention the B2 certificate, its cutoff, or any positivity statement. -/
def SuzukiYoshidaExponentialFormCoreSourceAt (r : Real) : Prop :=
  ∀ (hr : 0 < r) (n : Int),
    ∃ hDomain :
        SuzukiLogFourierDomain (suzukiYoshidaExponentialL2 r hr n),
      ∃ approximation : Nat → SuzukiSmoothCore r,
        Tendsto
          (fun k => suzukiSmoothCoreToLogGraph (approximation k))
          atTop
          (𝓝 (suzukiYoshidaExponentialLogGraph hr n hDomain))

/-- A source-core approximation sequence places the corresponding periodic
exponential in the legacy logarithmic radius completion. -/
theorem exists_suzukiYoshidaExponentialLogRadiusCompletion
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    ∃ v : SuzukiLogRadiusCompletion r,
      suzukiLogRadiusCompletionToL2 v =
        suzukiYoshidaExponentialL2 r hr n := by
  obtain ⟨hDomain, approximation, happroximation⟩ := hsource hr n
  let target : SuzukiLogGraphSpace :=
    suzukiYoshidaExponentialLogGraph hr n hDomain
  have htarget :
      target ∈ closure
        (Set.range (suzukiSmoothCoreToLogGraph (r := r))) := by
    apply mem_closure_of_tendsto happroximation
    exact Filter.Eventually.of_forall fun k =>
      Set.mem_range_self (approximation k)
  exact
    ⟨⟨target, htarget⟩, rfl⟩

/-- Hilbert-completion version of the source-core lift. -/
theorem exists_suzukiYoshidaExponentialLogRadiusLinearCompletion
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    ∃ v : SuzukiLogRadiusLinearCompletion r,
      suzukiLogRadiusLinearCompletionToL2 v =
        suzukiYoshidaExponentialL2 r hr n := by
  obtain ⟨v, hv⟩ :=
    exists_suzukiYoshidaExponentialLogRadiusCompletion
      hsource hr n
  exact
    ⟨suzukiLogRadiusCompletionToLinear v, hv⟩

/-- Every one of the 45 even endpoint modes has a lift once the exact
periodic-exponential source theorem is supplied. -/
theorem exists_suzukiYoshidaEvenLogRadiusLinearCompletion_fin45
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) :
    ∀ i : Fin 45, ∃ v : SuzukiLogRadiusLinearCompletion r,
      suzukiLogRadiusLinearCompletionToL2 v =
        suzukiYoshidaEvenL2 r hr i.1 := by
  intro i
  by_cases hi : i.1 = 0
  · obtain ⟨v, hv⟩ :=
      exists_suzukiYoshidaExponentialLogRadiusLinearCompletion
        hsource hr 0
    exact ⟨v, by simp [suzukiYoshidaEvenL2, hi, hv]⟩
  · obtain ⟨vPos, hvPos⟩ :=
      exists_suzukiYoshidaExponentialLogRadiusLinearCompletion
        hsource hr (i.1 : Int)
    obtain ⟨vNeg, hvNeg⟩ :=
      exists_suzukiYoshidaExponentialLogRadiusLinearCompletion
        hsource hr (-(i.1 : Int))
    refine
      ⟨((Real.sqrt 2)⁻¹ : Complex) • (vPos + vNeg), ?_⟩
    rw [suzukiYoshidaEvenL2, dif_neg hi, map_smul, map_add,
      hvPos, hvNeg]

/-- Every one of the 44 odd endpoint modes has a lift once the exact
periodic-exponential source theorem is supplied. -/
theorem exists_suzukiYoshidaOddLogRadiusLinearCompletion_fin44
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) :
    ∀ i : Fin 44, ∃ v : SuzukiLogRadiusLinearCompletion r,
      suzukiLogRadiusLinearCompletionToL2 v =
        suzukiYoshidaOddL2 r hr (i.1 + 1) := by
  intro i
  obtain ⟨vPos, hvPos⟩ :=
    exists_suzukiYoshidaExponentialLogRadiusLinearCompletion
      hsource hr (i.1 + 1 : Nat)
  obtain ⟨vNeg, hvNeg⟩ :=
    exists_suzukiYoshidaExponentialLogRadiusLinearCompletion
      hsource hr (-(i.1 + 1 : Nat))
  refine
    ⟨((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) •
        (vPos - vNeg), ?_⟩
  rw [suzukiYoshidaOddL2, map_smul, map_sub, hvPos, hvNeg]

/-- The B2 endpoint-mode certificate with the raw per-mode membership
premises discharged by Suzuki's exact periodic-exponential source theorem. -/
noncomputable def suzukiB2EndpointModeCertificateOfSource
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) :
    SuzukiB2EndpointModeCertificate r :=
  suzukiB2EndpointModeCertificateOfMembership hr
    (exists_suzukiYoshidaEvenLogRadiusLinearCompletion_fin45
      hsource hr)
    (exists_suzukiYoshidaOddLogRadiusLinearCompletion_fin44
      hsource hr)

/-- Frozen-project endpoint certificate obtained from the exact source
theorem, with no remaining individual mode-lift hypotheses. -/
noncomputable def suzukiProjectB2EndpointModeCertificateOfSource
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiB2EndpointModeCertificate suzukiProjectAStar :=
  suzukiB2EndpointModeCertificateOfSource hsource
    suzukiProjectAStar_pos

variable {ι : Type*} [Fintype ι]

/-- Finite reconstruction taking values in the logarithmic completion. -/
def suzukiFiniteCompletionReconstruction
    {r : Real} (mode : ι → SuzukiLogRadiusLinearCompletion r) :
    EuclideanSpace Complex ι →L[Complex]
      SuzukiLogRadiusLinearCompletion r :=
  ∑ i, (EuclideanSpace.proj i).smulRight (mode i)

@[simp]
theorem suzukiFiniteCompletionReconstruction_apply
    {r : Real} (mode : ι → SuzukiLogRadiusLinearCompletion r)
    (x : EuclideanSpace Complex ι) :
    suzukiFiniteCompletionReconstruction mode x =
      ∑ i, x i • mode i := by
  simp [suzukiFiniteCompletionReconstruction]

/-- The completion-valued finite low projection.  Its coordinates are the
already checked ambient-`L²` coordinates, while reconstruction uses the
chosen completion lifts. -/
def suzukiFiniteCompletionLowProjection
    {r : Real} (mode : ι → SuzukiLogRadiusLinearCompletion r) :
    SuzukiLogRadiusLinearCompletion r →L[Complex]
      SuzukiLogRadiusLinearCompletion r :=
  (suzukiFiniteCompletionReconstruction mode).comp
    ((suzukiFiniteL2CoordinateMap
      (fun i => suzukiLogRadiusLinearCompletionToL2 (mode i))).comp
        suzukiLogRadiusLinearCompletionToL2)

/-- The completion-valued far complement `id - P`. -/
def suzukiFiniteCompletionFarRemainder
    {r : Real} (mode : ι → SuzukiLogRadiusLinearCompletion r) :
    SuzukiLogRadiusLinearCompletion r →L[Complex]
      SuzukiLogRadiusLinearCompletion r :=
  ContinuousLinearMap.id Complex (SuzukiLogRadiusLinearCompletion r) -
    suzukiFiniteCompletionLowProjection mode

/-- Completion-valued reconstruction commutes exactly with the faithful
completion-to-`L²` embedding. -/
theorem suzukiLogRadiusLinearCompletionToL2_reconstruction
    {r : Real} (mode : ι → SuzukiLogRadiusLinearCompletion r)
    (x : EuclideanSpace Complex ι) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiFiniteCompletionReconstruction mode x) =
      suzukiFiniteL2Reconstruction
        (fun i => suzukiLogRadiusLinearCompletionToL2 (mode i)) x := by
  simp

/-- The completion low projection is carried to B2's ambient low projection
by the faithful completion-to-`L²` embedding. -/
theorem suzukiLogRadiusLinearCompletionToL2_lowProjection
    {r : Real} (mode : ι → SuzukiLogRadiusLinearCompletion r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiFiniteCompletionLowProjection mode v) =
      suzukiFiniteL2LowProjection
        (fun i => suzukiLogRadiusLinearCompletionToL2 (mode i))
        (suzukiLogRadiusLinearCompletionToL2 v) := by
  simp [suzukiFiniteCompletionLowProjection,
    suzukiFiniteL2LowProjection]

/-- The completion far complement is carried to B2's ambient far remainder
by the faithful completion-to-`L²` embedding. -/
theorem suzukiLogRadiusLinearCompletionToL2_farRemainder
    {r : Real} (mode : ι → SuzukiLogRadiusLinearCompletion r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiFiniteCompletionFarRemainder mode v) =
      suzukiFiniteL2FarRemainder
        (fun i => suzukiLogRadiusLinearCompletionToL2 (mode i))
        (suzukiLogRadiusLinearCompletionToL2 v) := by
  rw [suzukiFiniteCompletionFarRemainder,
    suzukiFiniteL2FarRemainder]
  change
    suzukiLogRadiusLinearCompletionToL2
        (v - suzukiFiniteCompletionLowProjection mode v) =
      suzukiLogRadiusLinearCompletionToL2 v -
        suzukiFiniteL2LowProjection
          (fun i => suzukiLogRadiusLinearCompletionToL2 (mode i))
          (suzukiLogRadiusLinearCompletionToL2 v)
  rw [map_sub,
    suzukiLogRadiusLinearCompletionToL2_lowProjection]

/-- Completion-valued low and far maps sum to the identity. -/
theorem suzukiFiniteCompletionLowProjection_add_farRemainder
    {r : Real} (mode : ι → SuzukiLogRadiusLinearCompletion r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiFiniteCompletionLowProjection mode v +
      suzukiFiniteCompletionFarRemainder mode v = v := by
  simp [suzukiFiniteCompletionFarRemainder]

/-- The frozen even completion-valued finite reconstruction. -/
def SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    EuclideanSpace Complex (Fin 45) →L[Complex]
      SuzukiLogRadiusLinearCompletion r :=
  suzukiFiniteCompletionReconstruction certificate.evenMode

/-- The frozen odd completion-valued finite reconstruction. -/
def SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    EuclideanSpace Complex (Fin 44) →L[Complex]
      SuzukiLogRadiusLinearCompletion r :=
  suzukiFiniteCompletionReconstruction certificate.oddMode

/-- The frozen even completion-valued low projection. -/
def SuzukiB2EndpointModeCertificate.evenLowProjectionCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    SuzukiLogRadiusLinearCompletion r →L[Complex]
      SuzukiLogRadiusLinearCompletion r :=
  suzukiFiniteCompletionLowProjection certificate.evenMode

/-- The frozen odd completion-valued low projection. -/
def SuzukiB2EndpointModeCertificate.oddLowProjectionCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    SuzukiLogRadiusLinearCompletion r →L[Complex]
      SuzukiLogRadiusLinearCompletion r :=
  suzukiFiniteCompletionLowProjection certificate.oddMode

/-- The frozen even completion-valued far complement. -/
def SuzukiB2EndpointModeCertificate.evenFarRemainderCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    SuzukiLogRadiusLinearCompletion r →L[Complex]
      SuzukiLogRadiusLinearCompletion r :=
  suzukiFiniteCompletionFarRemainder certificate.evenMode

/-- The frozen odd completion-valued far complement. -/
def SuzukiB2EndpointModeCertificate.oddFarRemainderCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    SuzukiLogRadiusLinearCompletion r →L[Complex]
      SuzukiLogRadiusLinearCompletion r :=
  suzukiFiniteCompletionFarRemainder certificate.oddMode

@[simp]
theorem SuzukiB2EndpointModeCertificate.toL2_evenReconstructionCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (x : EuclideanSpace Complex (Fin 45)) :
    suzukiLogRadiusLinearCompletionToL2
        (certificate.evenReconstructionCompletion x) =
      suzukiFiniteL2Reconstruction
        (fun i => suzukiLogRadiusLinearCompletionToL2
          (certificate.evenMode i)) x :=
  suzukiLogRadiusLinearCompletionToL2_reconstruction
    certificate.evenMode x

@[simp]
theorem SuzukiB2EndpointModeCertificate.toL2_oddReconstructionCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (x : EuclideanSpace Complex (Fin 44)) :
    suzukiLogRadiusLinearCompletionToL2
        (certificate.oddReconstructionCompletion x) =
      suzukiFiniteL2Reconstruction
        (fun i => suzukiLogRadiusLinearCompletionToL2
          (certificate.oddMode i)) x :=
  suzukiLogRadiusLinearCompletionToL2_reconstruction
    certificate.oddMode x

@[simp]
theorem SuzukiB2EndpointModeCertificate.toL2_evenLowProjectionCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompletionToL2
        (certificate.evenLowProjectionCompletion v) =
      suzukiFiniteL2LowProjection
        (fun i => suzukiLogRadiusLinearCompletionToL2
          (certificate.evenMode i))
        (suzukiLogRadiusLinearCompletionToL2 v) :=
  suzukiLogRadiusLinearCompletionToL2_lowProjection
    certificate.evenMode v

@[simp]
theorem SuzukiB2EndpointModeCertificate.toL2_oddLowProjectionCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompletionToL2
        (certificate.oddLowProjectionCompletion v) =
      suzukiFiniteL2LowProjection
        (fun i => suzukiLogRadiusLinearCompletionToL2
          (certificate.oddMode i))
        (suzukiLogRadiusLinearCompletionToL2 v) :=
  suzukiLogRadiusLinearCompletionToL2_lowProjection
    certificate.oddMode v

@[simp]
theorem SuzukiB2EndpointModeCertificate.toL2_evenFarRemainderCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompletionToL2
        (certificate.evenFarRemainderCompletion v) =
      certificate.evenFarRemainder v :=
  suzukiLogRadiusLinearCompletionToL2_farRemainder
    certificate.evenMode v

@[simp]
theorem SuzukiB2EndpointModeCertificate.toL2_oddFarRemainderCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompletionToL2
        (certificate.oddFarRemainderCompletion v) =
      certificate.oddFarRemainder v :=
  suzukiLogRadiusLinearCompletionToL2_farRemainder
    certificate.oddMode v

end

end M100
end Experiments
end RiemannHypothesisProject
