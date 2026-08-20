import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCompleteFormBlocks
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaExponentialPairingBridge
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaIntervalCompleteness

/-!
# M100-DF6D5B3T parity-far receiving spaces

The original B3 far and cross targets accepted arbitrary elements of the
logarithmic completion.  Removing an even low projection from such an element
does not remove its odd component, and conversely.  This module replaces those
targets by closed matching-parity far subspaces.

The corrected far target uses the physical ambient `L²` norm.  The form is an
explicit parameter, so the later B3V normalization can instantiate these
targets with the corrected source form rather than the legacy graph form.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set
open scoped ComplexConjugate Topology

/-- The closed even graph-completion sector with all retained even
coordinates equal to zero. -/
def SuzukiB2EndpointModeCertificate.evenParityFarSubspace
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    Submodule Complex (SuzukiLogRadiusLinearCompletion r) :=
  ((suzukiLogRadiusLinearReflection r).toContinuousLinearMap -
      ContinuousLinearMap.id Complex
        (SuzukiLogRadiusLinearCompletion r)).ker ⊓
    certificate.evenCoordinateMap.ker

/-- The closed odd graph-completion sector with all retained odd coordinates
equal to zero. -/
def SuzukiB2EndpointModeCertificate.oddParityFarSubspace
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    Submodule Complex (SuzukiLogRadiusLinearCompletion r) :=
  ((suzukiLogRadiusLinearReflection r).toContinuousLinearMap +
      ContinuousLinearMap.id Complex
        (SuzukiLogRadiusLinearCompletion r)).ker ⊓
    certificate.oddCoordinateMap.ker

/-- The even parity-far subspace is topologically closed in the live graph
completion. -/
theorem SuzukiB2EndpointModeCertificate.isClosed_evenParityFarSubspace
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    IsClosed (certificate.evenParityFarSubspace : Set
      (SuzukiLogRadiusLinearCompletion r)) := by
  exact
    (((suzukiLogRadiusLinearReflection r).toContinuousLinearMap -
        ContinuousLinearMap.id Complex
          (SuzukiLogRadiusLinearCompletion r)).isClosed_ker).inter
      certificate.evenCoordinateMap.isClosed_ker

/-- The odd parity-far subspace is topologically closed in the live graph
completion. -/
theorem SuzukiB2EndpointModeCertificate.isClosed_oddParityFarSubspace
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    IsClosed (certificate.oddParityFarSubspace : Set
      (SuzukiLogRadiusLinearCompletion r)) := by
  exact
    (((suzukiLogRadiusLinearReflection r).toContinuousLinearMap +
        ContinuousLinearMap.id Complex
          (SuzukiLogRadiusLinearCompletion r)).isClosed_ker).inter
      certificate.oddCoordinateMap.isClosed_ker

/-- A completion element is in the even parity-far subspace exactly when it
is reflection-fixed and has vanishing retained even coordinates. -/
theorem SuzukiB2EndpointModeCertificate.mem_evenParityFarSubspace_iff
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    v ∈ certificate.evenParityFarSubspace ↔
      suzukiLogRadiusLinearReflection r v = v ∧
        certificate.evenCoordinateMap v = 0 := by
  simp [SuzukiB2EndpointModeCertificate.evenParityFarSubspace,
    sub_eq_zero]

/-- A completion element is in the odd parity-far subspace exactly when its
reflection is its negative and its retained odd coordinates vanish. -/
theorem SuzukiB2EndpointModeCertificate.mem_oddParityFarSubspace_iff
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    v ∈ certificate.oddParityFarSubspace ↔
      suzukiLogRadiusLinearReflection r v = -v ∧
        certificate.oddCoordinateMap v = 0 := by
  simp [SuzukiB2EndpointModeCertificate.oddParityFarSubspace,
    add_eq_zero_iff_eq_neg]

/-- The concrete type of even parity-far completion elements. -/
abbrev SuzukiB2EndpointModeCertificate.EvenParityFarCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :=
  certificate.evenParityFarSubspace

/-- The concrete type of odd parity-far completion elements. -/
abbrev SuzukiB2EndpointModeCertificate.OddParityFarCompletion
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :=
  certificate.oddParityFarSubspace

/-- The physical `L²` image of the even parity-far graph subspace. -/
def SuzukiB2EndpointModeCertificate.evenParityFarL2Subspace
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    Submodule Complex SuzukiL2 :=
  certificate.evenParityFarSubspace.map
    suzukiLogRadiusLinearCompletionToL2.toLinearMap

/-- The physical `L²` image of the odd parity-far graph subspace. -/
def SuzukiB2EndpointModeCertificate.oddParityFarL2Subspace
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    Submodule Complex SuzukiL2 :=
  certificate.oddParityFarSubspace.map
    suzukiLogRadiusLinearCompletionToL2.toLinearMap

/-- The set-valued even image used by B3T is the carrier of the corresponding
linear image subspace. -/
theorem SuzukiB2EndpointModeCertificate.range_evenParityFar_toL2
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    Set.range (fun v : certificate.EvenParityFarCompletion =>
      suzukiLogRadiusLinearCompletionToL2 v.1) =
      (certificate.evenParityFarL2Subspace : Set SuzukiL2) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.1, w.2, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩

/-- The set-valued odd image used by B3T is the carrier of the corresponding
linear image subspace. -/
theorem SuzukiB2EndpointModeCertificate.range_oddParityFar_toL2
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r) :
    Set.range (fun v : certificate.OddParityFarCompletion =>
      suzukiLogRadiusLinearCompletionToL2 v.1) =
      (certificate.oddParityFarL2Subspace : Set SuzukiL2) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.1, w.2, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩

/-! ## Matching-parity complements -/

/-- Every chosen even low mode is reflection-fixed in the graph completion. -/
theorem SuzukiB2EndpointModeCertificate.evenMode_reflection
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (i : Fin 45) :
    suzukiLogRadiusLinearReflection r (certificate.evenMode i) =
      certificate.evenMode i := by
  apply suzukiLogRadiusLinearCompletionToL2_injective r
  rw [suzukiLogRadiusLinearCompletionToL2_reflection]
  exact certificate.evenParity i

/-- Every chosen odd low mode is reflection-anti-fixed in the graph
completion. -/
theorem SuzukiB2EndpointModeCertificate.oddMode_reflection
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (i : Fin 44) :
    suzukiLogRadiusLinearReflection r (certificate.oddMode i) =
      -certificate.oddMode i := by
  apply suzukiLogRadiusLinearCompletionToL2_injective r
  rw [suzukiLogRadiusLinearCompletionToL2_reflection, map_neg]
  exact certificate.oddParity i

/-- The even low reconstruction is reflection-fixed. -/
theorem SuzukiB2EndpointModeCertificate.evenReconstructionCompletion_reflection
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (x : EuclideanSpace Complex (Fin 45)) :
    suzukiLogRadiusLinearReflection r
        (certificate.evenReconstructionCompletion x) =
      certificate.evenReconstructionCompletion x := by
  classical
  rw [SuzukiB2EndpointModeCertificate.evenReconstructionCompletion,
    suzukiFiniteCompletionReconstruction_apply]
  induction (Finset.univ : Finset (Fin 45)) using Finset.induction_on with
  | empty => exact (suzukiLogRadiusLinearReflection r).map_zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi,
        (suzukiLogRadiusLinearReflection r).map_add,
        (suzukiLogRadiusLinearReflection r).map_smul,
        certificate.evenMode_reflection i, ih]

/-- The odd low reconstruction is reflection-anti-fixed. -/
theorem SuzukiB2EndpointModeCertificate.oddReconstructionCompletion_reflection
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (x : EuclideanSpace Complex (Fin 44)) :
    suzukiLogRadiusLinearReflection r
        (certificate.oddReconstructionCompletion x) =
      -certificate.oddReconstructionCompletion x := by
  classical
  rw [SuzukiB2EndpointModeCertificate.oddReconstructionCompletion,
    suzukiFiniteCompletionReconstruction_apply]
  calc
    suzukiLogRadiusLinearReflection r
        (∑ i, x i • certificate.oddMode i) =
      ∑ i, suzukiLogRadiusLinearReflection r
        (x i • certificate.oddMode i) := by
          change
            (suzukiLogRadiusLinearReflection r).toLinearMap
                (∑ i, x i • certificate.oddMode i) =
              ∑ i, (suzukiLogRadiusLinearReflection r).toLinearMap
                (x i • certificate.oddMode i)
          rw [map_sum]
    _ = ∑ i, -(x i • certificate.oddMode i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(suzukiLogRadiusLinearReflection r).map_smul,
        certificate.oddMode_reflection i, smul_neg]
    _ = -(∑ i, x i • certificate.oddMode i) := by
      rw [Finset.sum_neg_distrib]

/-- The even low projection always takes values in the even sector. -/
theorem SuzukiB2EndpointModeCertificate.evenLowProjectionCompletion_reflection
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearReflection r
        (certificate.evenLowProjectionCompletion v) =
      certificate.evenLowProjectionCompletion v := by
  exact certificate.evenReconstructionCompletion_reflection
    (certificate.evenCoordinateMap v)

/-- The odd low projection always takes values in the odd sector. -/
theorem SuzukiB2EndpointModeCertificate.oddLowProjectionCompletion_reflection
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearReflection r
        (certificate.oddLowProjectionCompletion v) =
      -certificate.oddLowProjectionCompletion v := by
  exact certificate.oddReconstructionCompletion_reflection
    (certificate.oddCoordinateMap v)

/-- Removing the even low block kills every retained even coordinate. -/
theorem SuzukiB2EndpointModeCertificate.evenCoordinateMap_farRemainder_zero
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    certificate.evenCoordinateMap
        (certificate.evenFarRemainderCompletion v) = 0 := by
  ext i
  rw [certificate.evenCoordinateMap_apply,
    certificate.toL2_evenFarRemainderCompletion]
  exact inner_suzukiFiniteL2Mode_farRemainder
    certificate.evenOrthonormal
    (suzukiLogRadiusLinearCompletionToL2 v) i

/-- Removing the odd low block kills every retained odd coordinate. -/
theorem SuzukiB2EndpointModeCertificate.oddCoordinateMap_farRemainder_zero
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    certificate.oddCoordinateMap
        (certificate.oddFarRemainderCompletion v) = 0 := by
  ext i
  rw [certificate.oddCoordinateMap_apply,
    certificate.toL2_oddFarRemainderCompletion]
  exact inner_suzukiFiniteL2Mode_farRemainder
    certificate.oddOrthonormal
    (suzukiLogRadiusLinearCompletionToL2 v) i

/-- The even far map preserves reflection-fixed inputs. -/
theorem SuzukiB2EndpointModeCertificate.evenFarRemainderCompletion_reflection
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    {v : SuzukiLogRadiusLinearCompletion r}
    (hv : suzukiLogRadiusLinearReflection r v = v) :
    suzukiLogRadiusLinearReflection r
        (certificate.evenFarRemainderCompletion v) =
      certificate.evenFarRemainderCompletion v := by
  rw [SuzukiB2EndpointModeCertificate.evenFarRemainderCompletion,
    suzukiFiniteCompletionFarRemainder]
  change
    suzukiLogRadiusLinearReflection r
        (v - certificate.evenLowProjectionCompletion v) =
      v - certificate.evenLowProjectionCompletion v
  rw [(suzukiLogRadiusLinearReflection r).map_sub, hv,
    certificate.evenLowProjectionCompletion_reflection]

/-- The odd far map preserves reflection-anti-fixed inputs. -/
theorem SuzukiB2EndpointModeCertificate.oddFarRemainderCompletion_reflection
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    {v : SuzukiLogRadiusLinearCompletion r}
    (hv : suzukiLogRadiusLinearReflection r v = -v) :
    suzukiLogRadiusLinearReflection r
        (certificate.oddFarRemainderCompletion v) =
      -certificate.oddFarRemainderCompletion v := by
  rw [SuzukiB2EndpointModeCertificate.oddFarRemainderCompletion,
    suzukiFiniteCompletionFarRemainder]
  change
    suzukiLogRadiusLinearReflection r
        (v - certificate.oddLowProjectionCompletion v) =
      -(v - certificate.oddLowProjectionCompletion v)
  rw [(suzukiLogRadiusLinearReflection r).map_sub, hv,
    certificate.oddLowProjectionCompletion_reflection]
  module

/-- The corrected even complement first projects to even parity and only then
removes the retained even modes. -/
def SuzukiB2EndpointModeCertificate.evenParityFarRemainder
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    certificate.EvenParityFarCompletion :=
  ⟨certificate.evenFarRemainderCompletion
      (suzukiLogRadiusLinearEvenProjector r v), by
    rw [certificate.mem_evenParityFarSubspace_iff]
    exact
      ⟨certificate.evenFarRemainderCompletion_reflection
          (suzukiLogRadiusLinearEvenProjector_reflection r v),
        certificate.evenCoordinateMap_farRemainder_zero _⟩⟩

/-- The corrected odd complement first projects to odd parity and only then
removes the retained odd modes. -/
def SuzukiB2EndpointModeCertificate.oddParityFarRemainder
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    certificate.OddParityFarCompletion :=
  ⟨certificate.oddFarRemainderCompletion
      (suzukiLogRadiusLinearOddProjector r v), by
    rw [certificate.mem_oddParityFarSubspace_iff]
    exact
      ⟨certificate.oddFarRemainderCompletion_reflection
          (suzukiLogRadiusLinearOddProjector_reflection r v),
        certificate.oddCoordinateMap_farRemainder_zero _⟩⟩

/-- Exact even reconstruction after the corrected parity-first split. -/
theorem SuzukiB2EndpointModeCertificate.evenParityLow_add_far
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    certificate.evenLowProjectionCompletion
        (suzukiLogRadiusLinearEvenProjector r v) +
      (certificate.evenParityFarRemainder v).1 =
        suzukiLogRadiusLinearEvenProjector r v := by
  exact suzukiFiniteCompletionLowProjection_add_farRemainder
    certificate.evenMode
    (suzukiLogRadiusLinearEvenProjector r v)

/-- Exact odd reconstruction after the corrected parity-first split. -/
theorem SuzukiB2EndpointModeCertificate.oddParityLow_add_far
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    certificate.oddLowProjectionCompletion
        (suzukiLogRadiusLinearOddProjector r v) +
      (certificate.oddParityFarRemainder v).1 =
        suzukiLogRadiusLinearOddProjector r v := by
  exact suzukiFiniteCompletionLowProjection_add_farRemainder
    certificate.oddMode
    (suzukiLogRadiusLinearOddProjector r v)

/-- Physical `L²` Pythagorean split of the corrected even parity block. -/
theorem SuzukiB2EndpointModeCertificate.evenParity_l2_norm_sq_split
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    ‖suzukiLogRadiusLinearCompletionToL2
        (suzukiLogRadiusLinearEvenProjector r v)‖ ^ 2 =
      ‖suzukiLogRadiusLinearCompletionToL2
        (certificate.evenLowProjectionCompletion
          (suzukiLogRadiusLinearEvenProjector r v))‖ ^ 2 +
      ‖suzukiLogRadiusLinearCompletionToL2
        (certificate.evenParityFarRemainder v).1‖ ^ 2 := by
  change
    ‖suzukiLogRadiusLinearCompletionToL2
        (suzukiLogRadiusLinearEvenProjector r v)‖ ^ 2 =
      ‖suzukiLogRadiusLinearCompletionToL2
        (certificate.evenLowProjectionCompletion
          (suzukiLogRadiusLinearEvenProjector r v))‖ ^ 2 +
      ‖suzukiLogRadiusLinearCompletionToL2
        (certificate.evenFarRemainderCompletion
          (suzukiLogRadiusLinearEvenProjector r v))‖ ^ 2
  rw [certificate.toL2_evenLowProjectionCompletion,
    certificate.toL2_evenFarRemainderCompletion]
  rw [suzukiFiniteL2LowProjection_norm_sq certificate.evenOrthonormal]
  exact certificate.even_parseval
    (suzukiLogRadiusLinearEvenProjector r v)

/-- Physical `L²` Pythagorean split of the corrected odd parity block. -/
theorem SuzukiB2EndpointModeCertificate.oddParity_l2_norm_sq_split
    {r : Real} (certificate : SuzukiB2EndpointModeCertificate r)
    (v : SuzukiLogRadiusLinearCompletion r) :
    ‖suzukiLogRadiusLinearCompletionToL2
        (suzukiLogRadiusLinearOddProjector r v)‖ ^ 2 =
      ‖suzukiLogRadiusLinearCompletionToL2
        (certificate.oddLowProjectionCompletion
          (suzukiLogRadiusLinearOddProjector r v))‖ ^ 2 +
      ‖suzukiLogRadiusLinearCompletionToL2
        (certificate.oddParityFarRemainder v).1‖ ^ 2 := by
  change
    ‖suzukiLogRadiusLinearCompletionToL2
        (suzukiLogRadiusLinearOddProjector r v)‖ ^ 2 =
      ‖suzukiLogRadiusLinearCompletionToL2
        (certificate.oddLowProjectionCompletion
          (suzukiLogRadiusLinearOddProjector r v))‖ ^ 2 +
      ‖suzukiLogRadiusLinearCompletionToL2
        (certificate.oddFarRemainderCompletion
          (suzukiLogRadiusLinearOddProjector r v))‖ ^ 2
  rw [certificate.toL2_oddLowProjectionCompletion,
    certificate.toL2_oddFarRemainderCompletion]
  rw [suzukiFiniteL2LowProjection_norm_sq certificate.oddOrthonormal]
  exact certificate.odd_parseval
    (suzukiLogRadiusLinearOddProjector r v)

/-! ## Ambient high-mode closures -/

/-- The ambient even Yoshida tail: the closed span of physical modes
`n ≥ 45`. -/
def suzukiDF6D5B3TEvenAmbientFarSubspace :
    Submodule Complex SuzukiL2 :=
  (Submodule.span Complex
    (Set.range fun n : {n : Nat // 45 ≤ n} =>
      suzukiYoshidaEvenL2 suzukiProjectAStar
        suzukiProjectAStar_pos n.1)).topologicalClosure

/-- The ambient odd Yoshida tail: the closed span of physical modes
`n ≥ 45`. -/
def suzukiDF6D5B3TOddAmbientFarSubspace :
    Submodule Complex SuzukiL2 :=
  (Submodule.span Complex
    (Set.range fun n : {n : Nat // 45 ≤ n} =>
      suzukiYoshidaOddL2 suzukiProjectAStar
        suzukiProjectAStar_pos n.1)).topologicalClosure

/-- The ambient even Yoshida tail is closed. -/
theorem isClosed_suzukiDF6D5B3TEvenAmbientFarSubspace :
    IsClosed (suzukiDF6D5B3TEvenAmbientFarSubspace : Set SuzukiL2) :=
  Submodule.isClosed_topologicalClosure _

/-- The ambient odd Yoshida tail is closed. -/
theorem isClosed_suzukiDF6D5B3TOddAmbientFarSubspace :
    IsClosed (suzukiDF6D5B3TOddAmbientFarSubspace : Set SuzukiL2) :=
  Submodule.isClosed_topologicalClosure _

/-- A supported even class with vanishing Yoshida coordinates `0, ..., 44`
belongs to the closed even tail generated by modes `n ≥ 45`. -/
theorem mem_suzukiDF6D5B3TEvenAmbientFarSubspace_of_supported_even_low_zero
    {v : SuzukiL2}
    (hsupport : suzukiL2SupportedAt suzukiProjectAStar v)
    (heven : SuzukiL2Even v)
    (hlow : ∀ i : Fin 45,
      inner Complex
        (suzukiYoshidaEvenL2 suzukiProjectAStar
          suzukiProjectAStar_pos i.1) v = 0) :
    v ∈ suzukiDF6D5B3TEvenAmbientFarSubspace := by
  let P : Submodule Complex SuzukiL2 :=
    suzukiL2SupportedSubmodule suzukiProjectAStar
  let E : Submodule Complex SuzukiL2 :=
    P ⊓
      (suzukiL2Reflection.toContinuousLinearMap -
        ContinuousLinearMap.id Complex SuzukiL2).ker
  let K : Submodule Complex SuzukiL2 :=
    Submodule.span Complex
      (Set.range fun n : {n : Nat // 45 ≤ n} =>
        suzukiYoshidaEvenL2 suzukiProjectAStar
          suzukiProjectAStar_pos n.1)
  have hKE : K.topologicalClosure ≤ E := by
    apply K.topologicalClosure_minimal
    · dsimp [K]
      rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      constructor
      · exact suzukiYoshidaEvenL2_mem_supportedSubmodule
          suzukiProjectAStar_pos n.1
      · apply sub_eq_zero.mpr
        exact suzukiYoshidaEvenL2_even suzukiProjectAStar_pos n.1
    · exact
        (isClosed_suzukiL2SupportedSubmodule suzukiProjectAStar).inter
          ((suzukiL2Reflection.toContinuousLinearMap -
            ContinuousLinearMap.id Complex SuzukiL2).isClosed_ker)
  have hlowOrth : ∀ i : Fin 45,
      suzukiYoshidaEvenL2 suzukiProjectAStar
          suzukiProjectAStar_pos i.1 ∈ K.topologicalClosureᗮ := by
    intro i
    rw [Submodule.orthogonal_closure]
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro y ⟨n, rfl⟩
      rw [inner_suzukiYoshidaEvenL2_eq_ite]
      rw [if_neg (by omega)]
    · simp
    · intro x y _ _ hx hy
      rw [inner_add_left, hx, hy, add_zero]
    · intro c x _ hx
      rw [inner_smul_left, hx, mul_zero]
  let w : SuzukiL2 := v - K.topologicalClosure.starProjection v
  have hprojectionE :
      K.topologicalClosure.starProjection v ∈ E :=
    hKE (K.topologicalClosure.starProjection_apply_mem v)
  have hwSupport :
      suzukiL2SupportedAt suzukiProjectAStar w := by
    exact P.sub_mem hsupport hprojectionE.1
  have hwEven : SuzukiL2Even w := by
    have hvE : v ∈ E := by
      exact ⟨hsupport, sub_eq_zero.mpr heven⟩
    have hwE : w ∈ E := E.sub_mem hvE hprojectionE
    exact sub_eq_zero.mp hwE.2
  have hwLow : ∀ i : Fin 45,
      inner Complex
        (suzukiYoshidaEvenL2 suzukiProjectAStar
          suzukiProjectAStar_pos i.1) w = 0 := by
    intro i
    rw [show w = v - K.topologicalClosure.starProjection v by rfl,
      inner_sub_right, hlow i]
    rw [Submodule.inner_left_of_mem_orthogonal
      (K.topologicalClosure.starProjection_apply_mem v) (hlowOrth i)]
    simp
  have hwHigh : ∀ n : Nat, 45 ≤ n →
      inner Complex
        (suzukiYoshidaEvenL2 suzukiProjectAStar
          suzukiProjectAStar_pos n) w = 0 := by
    intro n hn
    exact Submodule.inner_right_of_mem_orthogonal
      (K.le_topologicalClosure
        (Submodule.subset_span
          (Set.mem_range_self (⟨n, hn⟩ : {n : Nat // 45 ≤ n}))))
      (K.topologicalClosure.sub_starProjection_mem_orthogonal v)
  have hwAll : ∀ n : Nat,
      inner Complex
        (suzukiYoshidaEvenL2 suzukiProjectAStar
          suzukiProjectAStar_pos n) w = 0 := by
    intro n
    by_cases hn : n < 45
    · exact hwLow ⟨n, hn⟩
    · exact hwHigh n (by omega)
  have hwZero : w = 0 :=
    eq_zero_of_supportedAt_of_even_of_forall_inner_even_eq_zero
      suzukiProjectAStar_pos w hwSupport hwEven hwAll
  have hvProjection :
      v = K.topologicalClosure.starProjection v :=
    sub_eq_zero.mp hwZero
  rw [suzukiDF6D5B3TEvenAmbientFarSubspace]
  change v ∈ K.topologicalClosure
  rw [hvProjection]
  exact K.topologicalClosure.starProjection_apply_mem v

/-- A supported odd class with vanishing Yoshida coordinates `1, ..., 44`
belongs to the closed odd tail generated by modes `n ≥ 45`. -/
theorem mem_suzukiDF6D5B3TOddAmbientFarSubspace_of_supported_odd_low_zero
    {v : SuzukiL2}
    (hsupport : suzukiL2SupportedAt suzukiProjectAStar v)
    (hodd : SuzukiL2Odd v)
    (hlow : ∀ i : Fin 44,
      inner Complex
        (suzukiYoshidaOddL2 suzukiProjectAStar
          suzukiProjectAStar_pos (i.1 + 1)) v = 0) :
    v ∈ suzukiDF6D5B3TOddAmbientFarSubspace := by
  let P : Submodule Complex SuzukiL2 :=
    suzukiL2SupportedSubmodule suzukiProjectAStar
  let O : Submodule Complex SuzukiL2 :=
    P ⊓
      (suzukiL2Reflection.toContinuousLinearMap +
        ContinuousLinearMap.id Complex SuzukiL2).ker
  let K : Submodule Complex SuzukiL2 :=
    Submodule.span Complex
      (Set.range fun n : {n : Nat // 45 ≤ n} =>
        suzukiYoshidaOddL2 suzukiProjectAStar
          suzukiProjectAStar_pos n.1)
  have hKO : K.topologicalClosure ≤ O := by
    apply K.topologicalClosure_minimal
    · dsimp [K]
      rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      constructor
      · exact suzukiYoshidaOddL2_mem_supportedSubmodule
          suzukiProjectAStar_pos n.1
      · apply add_eq_zero_iff_eq_neg.mpr
        exact suzukiYoshidaOddL2_odd suzukiProjectAStar_pos n.1
    · exact
        (isClosed_suzukiL2SupportedSubmodule suzukiProjectAStar).inter
          ((suzukiL2Reflection.toContinuousLinearMap +
            ContinuousLinearMap.id Complex SuzukiL2).isClosed_ker)
  have hlowOrth : ∀ i : Fin 44,
      suzukiYoshidaOddL2 suzukiProjectAStar
          suzukiProjectAStar_pos (i.1 + 1) ∈
        K.topologicalClosureᗮ := by
    intro i
    rw [Submodule.orthogonal_closure]
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro y ⟨n, rfl⟩
      rw [inner_suzukiYoshidaOddL2_eq_ite
        suzukiProjectAStar_pos (by omega) (by omega)]
      rw [if_neg (by omega)]
    · simp
    · intro x y _ _ hx hy
      rw [inner_add_left, hx, hy, add_zero]
    · intro c x _ hx
      rw [inner_smul_left, hx, mul_zero]
  let w : SuzukiL2 := v - K.topologicalClosure.starProjection v
  have hprojectionO :
      K.topologicalClosure.starProjection v ∈ O :=
    hKO (K.topologicalClosure.starProjection_apply_mem v)
  have hwSupport :
      suzukiL2SupportedAt suzukiProjectAStar w := by
    exact P.sub_mem hsupport hprojectionO.1
  have hwOdd : SuzukiL2Odd w := by
    have hvO : v ∈ O := by
      exact ⟨hsupport, add_eq_zero_iff_eq_neg.mpr hodd⟩
    have hwO : w ∈ O := O.sub_mem hvO hprojectionO
    exact add_eq_zero_iff_eq_neg.mp hwO.2
  have hwLow : ∀ i : Fin 44,
      inner Complex
        (suzukiYoshidaOddL2 suzukiProjectAStar
          suzukiProjectAStar_pos (i.1 + 1)) w = 0 := by
    intro i
    rw [show w = v - K.topologicalClosure.starProjection v by rfl,
      inner_sub_right, hlow i]
    rw [Submodule.inner_left_of_mem_orthogonal
      (K.topologicalClosure.starProjection_apply_mem v) (hlowOrth i)]
    simp
  have hwHigh : ∀ n : Nat, 45 ≤ n →
      inner Complex
        (suzukiYoshidaOddL2 suzukiProjectAStar
          suzukiProjectAStar_pos n) w = 0 := by
    intro n hn
    exact Submodule.inner_right_of_mem_orthogonal
      (K.le_topologicalClosure
        (Submodule.subset_span
          (Set.mem_range_self (⟨n, hn⟩ : {n : Nat // 45 ≤ n}))))
      (K.topologicalClosure.sub_starProjection_mem_orthogonal v)
  have hwAll : ∀ n : Nat, 0 < n →
      inner Complex
        (suzukiYoshidaOddL2 suzukiProjectAStar
          suzukiProjectAStar_pos n) w = 0 := by
    intro n hn
    by_cases hn45 : n < 45
    · simpa [show n - 1 + 1 = n by omega] using
        hwLow (⟨n - 1, by omega⟩ : Fin 44)
    · exact hwHigh n (by omega)
  have hwZero : w = 0 :=
    eq_zero_of_supportedAt_of_odd_of_forall_inner_odd_eq_zero
      suzukiProjectAStar_pos w hwSupport hwOdd hwAll
  have hvProjection :
      v = K.topologicalClosure.starProjection v :=
    sub_eq_zero.mp hwZero
  rw [suzukiDF6D5B3TOddAmbientFarSubspace]
  change v ∈ K.topologicalClosure
  rw [hvProjection]
  exact K.topologicalClosure.starProjection_apply_mem v

/-! ## Identification of the source-certificate images -/

/-- Every physical image of the source certificate's even parity-far graph
subspace belongs to the ambient even Yoshida tail. -/
theorem suzukiProjectB3T_evenParityFarL2Subspace_le_ambient_of_source
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiB2EndpointModeCertificate.evenParityFarL2Subspace
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) ≤
      suzukiDF6D5B3TEvenAmbientFarSubspace := by
  let certificate :=
    suzukiProjectB2EndpointModeCertificateOfSource hsource
  rintro v ⟨w, hw, rfl⟩
  have hwProperties :=
    (certificate.mem_evenParityFarSubspace_iff w).mp hw
  apply
    mem_suzukiDF6D5B3TEvenAmbientFarSubspace_of_supported_even_low_zero
  · exact suzukiLogRadiusLinearCompletionToL2_supportedAt w
  · calc
      suzukiL2Reflection
          (suzukiLogRadiusLinearCompletionToL2 w) =
        suzukiLogRadiusLinearCompletionToL2
          (suzukiLogRadiusLinearReflection suzukiProjectAStar w) :=
            (suzukiLogRadiusLinearCompletionToL2_reflection
              suzukiProjectAStar w).symm
      _ = suzukiLogRadiusLinearCompletionToL2 w := by
        rw [hwProperties.1]
  · intro i
    have hi := congrArg (fun x => x i) hwProperties.2
    rw [certificate.evenCoordinateMap_apply,
      suzukiProjectB2EndpointModeCertificateOfSource_evenMode_eq,
      suzukiYoshidaEvenLinearCompletionOfSource_toL2] at hi
    simpa using hi

/-- Every physical image of the source certificate's odd parity-far graph
subspace belongs to the ambient odd Yoshida tail. -/
theorem suzukiProjectB3T_oddParityFarL2Subspace_le_ambient_of_source
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiB2EndpointModeCertificate.oddParityFarL2Subspace
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) ≤
      suzukiDF6D5B3TOddAmbientFarSubspace := by
  let certificate :=
    suzukiProjectB2EndpointModeCertificateOfSource hsource
  rintro v ⟨w, hw, rfl⟩
  have hwProperties :=
    (certificate.mem_oddParityFarSubspace_iff w).mp hw
  apply
    mem_suzukiDF6D5B3TOddAmbientFarSubspace_of_supported_odd_low_zero
  · exact suzukiLogRadiusLinearCompletionToL2_supportedAt w
  · calc
      suzukiL2Reflection
          (suzukiLogRadiusLinearCompletionToL2 w) =
        suzukiLogRadiusLinearCompletionToL2
          (suzukiLogRadiusLinearReflection suzukiProjectAStar w) :=
            (suzukiLogRadiusLinearCompletionToL2_reflection
              suzukiProjectAStar w).symm
      _ = -suzukiLogRadiusLinearCompletionToL2 w := by
        rw [hwProperties.1, map_neg]
  · intro i
    have hi := congrArg (fun x => x i) hwProperties.2
    rw [certificate.oddCoordinateMap_apply,
      suzukiProjectB2EndpointModeCertificateOfSource_oddMode_eq,
      suzukiYoshidaOddLinearCompletionOfSource_toL2] at hi
    simpa using hi

/-- Every even Yoshida mode in the physical tail has its canonical B2S lift
inside the source certificate's even parity-far graph subspace. -/
theorem suzukiYoshidaEvenL2_mem_source_evenParityFarL2Subspace
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (n : {n : Nat // 45 ≤ n}) :
    suzukiYoshidaEvenL2 suzukiProjectAStar
        suzukiProjectAStar_pos n.1 ∈
      SuzukiB2EndpointModeCertificate.evenParityFarL2Subspace
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  let certificate :=
    suzukiProjectB2EndpointModeCertificateOfSource hsource
  let w :=
    suzukiYoshidaEvenLinearCompletionOfSource
      hsource suzukiProjectAStar_pos n.1
  refine ⟨w, ?_, ?_⟩
  · change w ∈ certificate.evenParityFarSubspace
    rw [certificate.mem_evenParityFarSubspace_iff]
    constructor
    · apply suzukiLogRadiusLinearCompletionToL2_injective
        suzukiProjectAStar
      rw [suzukiLogRadiusLinearCompletionToL2_reflection]
      rw [show
        suzukiLogRadiusLinearCompletionToL2 w =
          suzukiYoshidaEvenL2 suzukiProjectAStar
            suzukiProjectAStar_pos n.1 by
          exact
            suzukiYoshidaEvenLinearCompletionOfSource_toL2
              hsource suzukiProjectAStar_pos n.1]
      exact suzukiYoshidaEvenL2_even suzukiProjectAStar_pos n.1
    · ext i
      rw [certificate.evenCoordinateMap_apply,
        suzukiProjectB2EndpointModeCertificateOfSource_evenMode_eq,
        suzukiYoshidaEvenLinearCompletionOfSource_toL2]
      change
        inner Complex
            (suzukiYoshidaEvenL2 suzukiProjectAStar
              suzukiProjectAStar_pos i.1)
            (suzukiLogRadiusLinearCompletionToL2 w) = 0
      rw [show
        suzukiLogRadiusLinearCompletionToL2 w =
          suzukiYoshidaEvenL2 suzukiProjectAStar
            suzukiProjectAStar_pos n.1 by
          exact
            suzukiYoshidaEvenLinearCompletionOfSource_toL2
              hsource suzukiProjectAStar_pos n.1]
      rw [inner_suzukiYoshidaEvenL2_eq_ite,
        if_neg (by omega)]
  · exact
      suzukiYoshidaEvenLinearCompletionOfSource_toL2
        hsource suzukiProjectAStar_pos n.1

/-- Every odd Yoshida mode in the physical tail has its canonical B2S lift
inside the source certificate's odd parity-far graph subspace. -/
theorem suzukiYoshidaOddL2_mem_source_oddParityFarL2Subspace
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (n : {n : Nat // 45 ≤ n}) :
    suzukiYoshidaOddL2 suzukiProjectAStar
        suzukiProjectAStar_pos n.1 ∈
      SuzukiB2EndpointModeCertificate.oddParityFarL2Subspace
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  let certificate :=
    suzukiProjectB2EndpointModeCertificateOfSource hsource
  let w :=
    suzukiYoshidaOddLinearCompletionOfSource
      hsource suzukiProjectAStar_pos n.1
  refine ⟨w, ?_, ?_⟩
  · change w ∈ certificate.oddParityFarSubspace
    rw [certificate.mem_oddParityFarSubspace_iff]
    constructor
    · apply suzukiLogRadiusLinearCompletionToL2_injective
        suzukiProjectAStar
      rw [suzukiLogRadiusLinearCompletionToL2_reflection, map_neg]
      change
        suzukiL2Reflection
            (suzukiLogRadiusLinearCompletionToL2 w) =
          -suzukiLogRadiusLinearCompletionToL2 w
      rw [show
        suzukiLogRadiusLinearCompletionToL2 w =
          suzukiYoshidaOddL2 suzukiProjectAStar
            suzukiProjectAStar_pos n.1 by
          exact
            suzukiYoshidaOddLinearCompletionOfSource_toL2
              hsource suzukiProjectAStar_pos n.1]
      exact suzukiYoshidaOddL2_odd suzukiProjectAStar_pos n.1
    · ext i
      rw [certificate.oddCoordinateMap_apply,
        suzukiProjectB2EndpointModeCertificateOfSource_oddMode_eq,
        suzukiYoshidaOddLinearCompletionOfSource_toL2]
      change
        inner Complex
            (suzukiYoshidaOddL2 suzukiProjectAStar
              suzukiProjectAStar_pos (i.1 + 1))
            (suzukiLogRadiusLinearCompletionToL2 w) = 0
      rw [show
        suzukiLogRadiusLinearCompletionToL2 w =
          suzukiYoshidaOddL2 suzukiProjectAStar
            suzukiProjectAStar_pos n.1 by
          exact
            suzukiYoshidaOddLinearCompletionOfSource_toL2
              hsource suzukiProjectAStar_pos n.1]
      rw [inner_suzukiYoshidaOddL2_eq_ite
          suzukiProjectAStar_pos (by omega) (by omega),
        if_neg (by omega)]
  · exact
      suzukiYoshidaOddLinearCompletionOfSource_toL2
        hsource suzukiProjectAStar_pos n.1

/-- Exact B3T density target for the even receiving space.  This proposition
keeps both containment and density visible: the graph-completion image must
land in, and be dense in, the ambient physical high-mode closure. -/
def SuzukiDF6D5B3TEvenParityFarImageDense
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  let image : Set SuzukiL2 :=
    Set.range fun v : certificate.EvenParityFarCompletion =>
      suzukiLogRadiusLinearCompletionToL2 v.1
  image ⊆ suzukiDF6D5B3TEvenAmbientFarSubspace ∧
    closure image =
      (suzukiDF6D5B3TEvenAmbientFarSubspace : Set SuzukiL2)

/-- Exact B3T density target for the odd receiving space. -/
def SuzukiDF6D5B3TOddParityFarImageDense
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  let image : Set SuzukiL2 :=
    Set.range fun v : certificate.OddParityFarCompletion =>
      suzukiLogRadiusLinearCompletionToL2 v.1
  image ⊆ suzukiDF6D5B3TOddAmbientFarSubspace ∧
    closure image =
      (suzukiDF6D5B3TOddAmbientFarSubspace : Set SuzukiL2)

/-- B3T even dense-image endpoint for the canonical B2S source certificate. -/
theorem suzukiProjectB3T_evenParityFarImageDense_of_source
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiDF6D5B3TEvenParityFarImageDense
      (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  let certificate :=
    suzukiProjectB2EndpointModeCertificateOfSource hsource
  let S : Submodule Complex SuzukiL2 :=
    certificate.evenParityFarL2Subspace
  have hSambient :
      S ≤ suzukiDF6D5B3TEvenAmbientFarSubspace := by
    exact
      suzukiProjectB3T_evenParityFarL2Subspace_le_ambient_of_source
        hsource
  have hclosure :
      S.topologicalClosure =
        suzukiDF6D5B3TEvenAmbientFarSubspace := by
    apply le_antisymm
    · exact S.topologicalClosure_minimal hSambient
        isClosed_suzukiDF6D5B3TEvenAmbientFarSubspace
    · rw [suzukiDF6D5B3TEvenAmbientFarSubspace]
      apply
        (Submodule.span Complex
          (Set.range fun n : {n : Nat // 45 ≤ n} =>
            suzukiYoshidaEvenL2 suzukiProjectAStar
              suzukiProjectAStar_pos n.1)).topologicalClosure_minimal
      · rw [Submodule.span_le]
        rintro _ ⟨n, rfl⟩
        exact S.le_topologicalClosure
          (suzukiYoshidaEvenL2_mem_source_evenParityFarL2Subspace
            hsource n)
      · exact Submodule.isClosed_topologicalClosure S
  unfold SuzukiDF6D5B3TEvenParityFarImageDense
  change
    Set.range (fun v : certificate.EvenParityFarCompletion =>
        suzukiLogRadiusLinearCompletionToL2 v.1) ⊆
          suzukiDF6D5B3TEvenAmbientFarSubspace ∧
      closure
          (Set.range (fun v : certificate.EvenParityFarCompletion =>
            suzukiLogRadiusLinearCompletionToL2 v.1)) =
        (suzukiDF6D5B3TEvenAmbientFarSubspace : Set SuzukiL2)
  rw [certificate.range_evenParityFar_toL2]
  constructor
  · exact hSambient
  · rw [← Submodule.topologicalClosure_coe, hclosure]

/-- B3T odd dense-image endpoint for the canonical B2S source certificate. -/
theorem suzukiProjectB3T_oddParityFarImageDense_of_source
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiDF6D5B3TOddParityFarImageDense
      (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  let certificate :=
    suzukiProjectB2EndpointModeCertificateOfSource hsource
  let S : Submodule Complex SuzukiL2 :=
    certificate.oddParityFarL2Subspace
  have hSambient :
      S ≤ suzukiDF6D5B3TOddAmbientFarSubspace := by
    exact
      suzukiProjectB3T_oddParityFarL2Subspace_le_ambient_of_source
        hsource
  have hclosure :
      S.topologicalClosure =
        suzukiDF6D5B3TOddAmbientFarSubspace := by
    apply le_antisymm
    · exact S.topologicalClosure_minimal hSambient
        isClosed_suzukiDF6D5B3TOddAmbientFarSubspace
    · rw [suzukiDF6D5B3TOddAmbientFarSubspace]
      apply
        (Submodule.span Complex
          (Set.range fun n : {n : Nat // 45 ≤ n} =>
            suzukiYoshidaOddL2 suzukiProjectAStar
              suzukiProjectAStar_pos n.1)).topologicalClosure_minimal
      · rw [Submodule.span_le]
        rintro _ ⟨n, rfl⟩
        exact S.le_topologicalClosure
          (suzukiYoshidaOddL2_mem_source_oddParityFarL2Subspace
            hsource n)
      · exact Submodule.isClosed_topologicalClosure S
  unfold SuzukiDF6D5B3TOddParityFarImageDense
  change
    Set.range (fun v : certificate.OddParityFarCompletion =>
        suzukiLogRadiusLinearCompletionToL2 v.1) ⊆
          suzukiDF6D5B3TOddAmbientFarSubspace ∧
      closure
          (Set.range (fun v : certificate.OddParityFarCompletion =>
            suzukiLogRadiusLinearCompletionToL2 v.1)) =
        (suzukiDF6D5B3TOddAmbientFarSubspace : Set SuzukiL2)
  rw [certificate.range_oddParityFar_toL2]
  constructor
  · exact hSambient
  · rw [← Submodule.topologicalClosure_coe, hclosure]

/-- Minimal wrapper for the Hermitian form that B3V will normalize. -/
structure SuzukiDF6D5B3THermitianForm where
  toFun :
    SuzukiLogRadiusLinearCompletion suzukiProjectAStar →
      SuzukiLogRadiusLinearCompletion suzukiProjectAStar → Complex
  conj_symm : ∀ u v, toFun u v = conj (toFun v u)

instance : CoeFun SuzukiDF6D5B3THermitianForm (fun _ =>
    SuzukiLogRadiusLinearCompletion suzukiProjectAStar →
      SuzukiLogRadiusLinearCompletion suzukiProjectAStar → Complex) where
  coe form := form.toFun

/-- Corrected even far-coercivity target.  Its quantified input is already in
the matching parity-far space, and its norm is the physical ambient `L²`
norm, not the graph-completion norm. -/
def SuzukiDF6D5B3TEvenFarCoercivity
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar)
    (form : SuzukiDF6D5B3THermitianForm) : Prop :=
  ∀ v : certificate.EvenParityFarCompletion,
    2 * ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 ≤
      (form v.1 v.1).re

/-- Corrected odd far-coercivity target. -/
def SuzukiDF6D5B3TOddFarCoercivity
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar)
    (form : SuzukiDF6D5B3THermitianForm) : Prop :=
  ∀ v : certificate.OddParityFarCompletion,
    2 * ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 ≤
      (form v.1 v.1).re

/-- Corrected even residual-to-cross target on the matching parity-far
receiving space. -/
def SuzukiDF6D5B3TEvenCrossEstimate
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar)
    (form : SuzukiDF6D5B3THermitianForm) : Prop :=
  ∀ (x : EuclideanSpace Complex (Fin 45))
      (v : certificate.EvenParityFarCompletion),
    ‖form (certificate.evenReconstructionCompletion x) v.1‖ ^ 2 ≤
      (5 / 2 : Real) * suzukiDF6D5EvenCouplingHermitianQuadratic x *
        (form v.1 v.1).re

/-- Corrected odd residual-to-cross target on the matching parity-far
receiving space. -/
def SuzukiDF6D5B3TOddCrossEstimate
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar)
    (form : SuzukiDF6D5B3THermitianForm) : Prop :=
  ∀ (x : EuclideanSpace Complex (Fin 44))
      (v : certificate.OddParityFarCompletion),
    ‖form (certificate.oddReconstructionCompletion x) v.1‖ ^ 2 ≤
      (5 / 2 : Real) * suzukiDF6D5OddCouplingHermitianQuadratic x *
        (form v.1 v.1).re

end

end RiemannHypothesisProject.Experiments.M100
