import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCorrectedForms
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaExponentialPairingBridge
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualEnclosures

/-!
# Corrected exponential kernel for M100-DF6D5B3Q

This module separates the explicit all-integer endpoint kernel from the
analytic theorem identifying it with the corrected closed source form.

The kernel is reconstructed from the exact even and odd DF6D4 entries.  It is
therefore not defined by evaluating the completed form.  The low-low and
low-high parity normalizations are algebraic consequences of this definition.
The source-limit identification remains a separate theorem family.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter Set
open scoped ComplexConjugate Topology

/-! ## Explicit parity entries -/

/-- The exact all-mode even entry underlying the frozen DF6D4 matrix and
actual coupling columns. -/
def suzukiYoshidaCorrectedEvenEntry (m n : Nat) : Real :=
  if m = n then
    suzukiDF6D4EvenDiagonalEntry m
  else
    suzukiDF6D4EvenOffDiagonal (min m n) (max m n)

/-- The exact positive-mode odd entry underlying the frozen DF6D4 matrix and
actual coupling columns.  Downstream odd uses always have positive indices. -/
def suzukiYoshidaCorrectedOddEntry (m n : Nat) : Real :=
  if m = n then
    suzukiDF6D4OddDiagonalEntry m
  else
    suzukiDF6D4OddOffDiagonal (min m n) (max m n)

theorem suzukiYoshidaCorrectedEvenEntry_comm (m n : Nat) :
    suzukiYoshidaCorrectedEvenEntry m n =
      suzukiYoshidaCorrectedEvenEntry n m := by
  by_cases h : m = n
  · subst n
    rfl
  · simp [suzukiYoshidaCorrectedEvenEntry, h, Ne.symm h,
      min_comm, max_comm]

theorem suzukiYoshidaCorrectedOddEntry_comm (m n : Nat) :
    suzukiYoshidaCorrectedOddEntry m n =
      suzukiYoshidaCorrectedOddEntry n m := by
  by_cases h : m = n
  · subst n
    rfl
  · simp [suzukiYoshidaCorrectedOddEntry, h, Ne.symm h,
      min_comm, max_comm]

/-! ## All-integer exponential kernel -/

/-- Explicit corrected-`F` endpoint kernel on the complex exponential basis.

For nonzero frequencies this is the inverse unitary transform of the exact
even and odd entries.  The zero-mode branches encode the exceptional
constant-mode normalization.  No completed-form evaluation occurs in this
definition. -/
def suzukiYoshidaCorrectedExplicitKernel (m n : Int) : Complex :=
  let even : Complex :=
    suzukiYoshidaCorrectedEvenEntry m.natAbs n.natAbs
  let odd : Complex :=
    suzukiYoshidaCorrectedOddEntry m.natAbs n.natAbs
  if _hm : m = 0 then
    if _hn : n = 0 then even
    else ((Real.sqrt 2)⁻¹ : Complex) * even
  else if _hn : n = 0 then
    ((Real.sqrt 2)⁻¹ : Complex) * even
  else if 0 < m ↔ 0 < n then
    (2 : Complex)⁻¹ * (even + odd)
  else
    (2 : Complex)⁻¹ * (even - odd)

private theorem suzukiYoshida_corrected_sqrtTwo_ne_zero :
    Real.sqrt 2 ≠ 0 := by
  positivity

private theorem suzukiYoshida_corrected_even_scalar_normalization :
    conj (((Real.sqrt 2)⁻¹ : Complex)) *
        (((Real.sqrt 2)⁻¹ : Complex) * 2) = 1 := by
  rw [map_inv₀, Complex.conj_ofReal]
  have hsquare : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsquareC :
      (((Real.sqrt 2 : Real) : Complex) ^ 2) = (2 : Complex) := by
    exact_mod_cast hsquare
  rw [← hsquareC]
  field_simp [suzukiYoshida_corrected_sqrtTwo_ne_zero]

private theorem suzukiYoshida_corrected_odd_scalar_normalization :
    conj (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
        (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) * 2) = 1 := by
  rw [map_inv₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
  have hsquare : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsquareC :
      (((Real.sqrt 2 : Real) : Complex) ^ 2) = (2 : Complex) := by
    exact_mod_cast hsquare
  rw [← hsquareC]
  field_simp [suzukiYoshida_corrected_sqrtTwo_ne_zero,
    Complex.I_ne_zero]
  rw [Complex.I_sq]

private theorem suzukiYoshida_corrected_even_scalar_sq :
    conj (((Real.sqrt 2)⁻¹ : Complex)) *
        ((Real.sqrt 2)⁻¹ : Complex) = (2 : Complex)⁻¹ := by
  calc
    conj (((Real.sqrt 2)⁻¹ : Complex)) *
          ((Real.sqrt 2)⁻¹ : Complex) =
        (2 : Complex)⁻¹ *
          (conj (((Real.sqrt 2)⁻¹ : Complex)) *
            (((Real.sqrt 2)⁻¹ : Complex) * 2)) := by ring
    _ = (2 : Complex)⁻¹ := by
      rw [suzukiYoshida_corrected_even_scalar_normalization]
      simp

private theorem suzukiYoshida_corrected_odd_scalar_sq :
    conj (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
        ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) =
      (2 : Complex)⁻¹ := by
  calc
    conj (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
          ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) =
        (2 : Complex)⁻¹ *
          (conj (((Complex.I *
              (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
            (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) * 2)) := by
              ring
    _ = (2 : Complex)⁻¹ := by
      rw [suzukiYoshida_corrected_odd_scalar_normalization]
      simp

theorem suzukiYoshidaEvenSourceKernelPairing_correctedExplicit
    (m n : Nat) :
    suzukiYoshidaEvenSourceKernelPairing
        suzukiYoshidaCorrectedExplicitKernel m n =
      (suzukiYoshidaCorrectedEvenEntry m n : Complex) := by
  unfold suzukiYoshidaEvenSourceKernelPairing
  by_cases hm : m = 0
  · subst m
    by_cases hn : n = 0
    · subst n
      simp [suzukiYoshidaCorrectedExplicitKernel]
    · simp only [if_pos, if_neg hn]
      simp [suzukiYoshidaCorrectedExplicitKernel, hn,
        suzukiYoshidaCorrectedEvenEntry_comm]
      calc
        ((Real.sqrt 2)⁻¹ : Complex) *
              (((Real.sqrt 2)⁻¹ : Complex) *
                  (suzukiYoshidaCorrectedEvenEntry n 0 : Complex) +
                ((Real.sqrt 2)⁻¹ : Complex) *
                  (suzukiYoshidaCorrectedEvenEntry n 0 : Complex)) =
            (conj (((Real.sqrt 2)⁻¹ : Complex)) *
              (((Real.sqrt 2)⁻¹ : Complex) * 2)) *
                (suzukiYoshidaCorrectedEvenEntry n 0 : Complex) := by
                  simp
                  ring
        _ = _ := by
          rw [suzukiYoshida_corrected_even_scalar_normalization]
          simp
  · by_cases hn : n = 0
    · subst n
      simp only [if_neg hm, if_pos]
      simp [suzukiYoshidaCorrectedExplicitKernel, hm,
        suzukiYoshidaCorrectedEvenEntry_comm]
      calc
        ((Real.sqrt 2)⁻¹ : Complex) *
              (((Real.sqrt 2)⁻¹ : Complex) *
                  (suzukiYoshidaCorrectedEvenEntry m 0 : Complex) +
                ((Real.sqrt 2)⁻¹ : Complex) *
                  (suzukiYoshidaCorrectedEvenEntry m 0 : Complex)) =
            (conj (((Real.sqrt 2)⁻¹ : Complex)) *
              (((Real.sqrt 2)⁻¹ : Complex) * 2)) *
                (suzukiYoshidaCorrectedEvenEntry m 0 : Complex) := by
                  simp
                  ring
        _ = _ := by
          rw [suzukiYoshida_corrected_even_scalar_normalization]
          simp
    · simp only [if_neg hm, if_neg hn]
      have hmNatPos : 0 < m := Nat.pos_of_ne_zero hm
      have hnNatPos : 0 < n := Nat.pos_of_ne_zero hn
      have hmNotNeg : ¬(m : Int) < 0 := by omega
      have hnNotNeg : ¬(n : Int) < 0 := by omega
      simp [suzukiYoshidaCorrectedExplicitKernel, hm, hn,
        hmNatPos, hnNatPos, hmNotNeg, hnNotNeg]
      rw [show
        ((Real.sqrt 2)⁻¹ : Complex) *
            ((Real.sqrt 2)⁻¹ : Complex) = (2 : Complex)⁻¹ by
          simpa using
            suzukiYoshida_corrected_even_scalar_sq]
      ring

theorem suzukiYoshidaOddSourceKernelPairing_correctedExplicit
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    suzukiYoshidaOddSourceKernelPairing
        suzukiYoshidaCorrectedExplicitKernel m n =
      (suzukiYoshidaCorrectedOddEntry m n : Complex) := by
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hmPos : (0 : Int) < (m : Int) := by exact_mod_cast hm
  have hnPos : (0 : Int) < (n : Int) := by exact_mod_cast hn
  have hmNotNeg : ¬(m : Int) < 0 := by omega
  have hnNotNeg : ¬(n : Int) < 0 := by omega
  unfold suzukiYoshidaOddSourceKernelPairing
  dsimp only
  rw [suzukiYoshida_corrected_odd_scalar_sq]
  simp [suzukiYoshidaCorrectedExplicitKernel, hm0, hn0, hm, hn,
    hmPos, hnPos, hmNotNeg, hnNotNeg]
  ring

/-! ## Low-low and low-high normalization -/

theorem suzukiYoshidaCorrectedEvenEntry_fin45
    (i j : Fin 45) :
    suzukiYoshidaCorrectedEvenEntry i.1 j.1 =
      suzukiDF6D4EvenEndpointMatrix i j := by
  simp [suzukiYoshidaCorrectedEvenEntry,
    suzukiDF6D4EvenEndpointMatrix]

theorem suzukiYoshidaCorrectedOddEntry_fin44
    (i j : Fin 44) :
    suzukiYoshidaCorrectedOddEntry (i.1 + 1) (j.1 + 1) =
      suzukiDF6D4OddEndpointMatrix i j := by
  simp [suzukiYoshidaCorrectedOddEntry,
    suzukiDF6D4OddEndpointMatrix]

theorem suzukiYoshidaCorrectedExplicitKernel_lowMatrixNormalization :
    SuzukiDF6D5B3PExponentialKernelNormalization
      suzukiYoshidaCorrectedExplicitKernel := by
  constructor
  · intro i j
    rw [suzukiYoshidaEvenSourceKernelPairing_correctedExplicit,
      suzukiYoshidaCorrectedEvenEntry_fin45]
  · intro i j
    rw [suzukiYoshidaOddSourceKernelPairing_correctedExplicit
        (by omega) (by omega),
      suzukiYoshidaCorrectedOddEntry_fin44]

theorem suzukiYoshidaCorrectedEvenEntry_low_high
    (i : Fin 45) (mode : Nat) (hmode : 45 ≤ mode) :
    suzukiYoshidaCorrectedEvenEntry
        (suzukiDF6D4EvenLowMode i) mode =
      suzukiDF6D4EvenOffDiagonal
        (suzukiDF6D4EvenLowMode i) mode := by
  unfold suzukiYoshidaCorrectedEvenEntry
  rw [if_neg (by
    unfold suzukiDF6D4EvenLowMode
    have := i.isLt
    omega)]
  have hle : suzukiDF6D4EvenLowMode i ≤ mode := by
    unfold suzukiDF6D4EvenLowMode
    have := i.isLt
    omega
  rw [Nat.min_eq_left hle, Nat.max_eq_right hle]

theorem suzukiYoshidaCorrectedOddEntry_low_high
    (i : Fin 44) (mode : Nat) (hmode : 45 ≤ mode) :
    suzukiYoshidaCorrectedOddEntry
        (suzukiDF6D4OddLowMode i) mode =
      suzukiDF6D4OddOffDiagonal
        (suzukiDF6D4OddLowMode i) mode := by
  unfold suzukiYoshidaCorrectedOddEntry
  rw [if_neg (by
    unfold suzukiDF6D4OddLowMode
    have := i.isLt
    omega)]
  have hle : suzukiDF6D4OddLowMode i ≤ mode := by
    unfold suzukiDF6D4OddLowMode
    have := i.isLt
    omega
  rw [Nat.min_eq_left hle, Nat.max_eq_right hle]

theorem suzukiYoshidaCorrectedExplicitKernel_evenCouplingColumn
    (i : Fin 45) (mode : Nat) (hmode : 45 ≤ mode) :
    suzukiYoshidaEvenSourceKernelPairing
        suzukiYoshidaCorrectedExplicitKernel
        (suzukiDF6D4EvenLowMode i) mode =
      (suzukiDF6D4EvenOffDiagonal
        (suzukiDF6D4EvenLowMode i) mode : Complex) := by
  rw [suzukiYoshidaEvenSourceKernelPairing_correctedExplicit,
    suzukiYoshidaCorrectedEvenEntry_low_high i mode hmode]

theorem suzukiYoshidaCorrectedExplicitKernel_oddCouplingColumn
    (i : Fin 44) (mode : Nat) (hmode : 45 ≤ mode) :
    suzukiYoshidaOddSourceKernelPairing
        suzukiYoshidaCorrectedExplicitKernel
        (suzukiDF6D4OddLowMode i) mode =
      (suzukiDF6D4OddOffDiagonal
        (suzukiDF6D4OddLowMode i) mode : Complex) := by
  rw [suzukiYoshidaOddSourceKernelPairing_correctedExplicit
      (by simp [suzukiDF6D4OddLowMode])
      (by omega),
    suzukiYoshidaCorrectedOddEntry_low_high i mode hmode]

/-! ## Source-side equation-(2.5) limit -/

/-- Every completed-domain vector admits a sequence from the exact linear
smooth core.  This is the sequential form of B3V's dense-range theorem. -/
theorem exists_suzukiYoshidaCorrectedSmoothCoreApproximation
    (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    ∃ approximation :
        Nat → SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar,
      Tendsto
        (fun k =>
          suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
            suzukiProjectAStar (approximation k))
        atTop (𝓝 u) := by
  have hdense :=
    suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_denseRange
      suzukiProjectAStar
  have hu :
      u ∈ closure
        (Set.range
          (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
            suzukiProjectAStar)) := by
    exact hdense u
  rw [mem_closure_iff_seq_limit] at hu
  obtain ⟨sequence, hsequenceRange, hsequence⟩ := hu
  choose approximation happ using hsequenceRange
  refine ⟨approximation, ?_⟩
  simpa only [happ] using hsequence

/-- A canonical dense-core approximation chosen for a completed vector. -/
noncomputable def suzukiYoshidaCorrectedSmoothCoreApproximation
    (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    Nat → SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar :=
  Classical.choose
    (exists_suzukiYoshidaCorrectedSmoothCoreApproximation u)

theorem suzukiYoshidaCorrectedSmoothCoreApproximation_tendsto
    (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    Tendsto
      (fun k =>
        suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar
          (suzukiYoshidaCorrectedSmoothCoreApproximation u k))
      atTop (𝓝 u) :=
  Classical.choose_spec
    (exists_suzukiYoshidaCorrectedSmoothCoreApproximation u)

/-- The diagonal screw-form expression appearing on the left of Suzuki's
equation (2.5), evaluated on the exact project smooth core. -/
def suzukiEquation25CoreQuadratic
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) : Complex :=
  (suzukiFiniteKernelPairing suzukiScrewFunction suzukiProjectAStar
    (suzukiSmoothCoreDifferential suzukiProjectAStar_pos
      (suzukiSmoothCoreLinearSubmoduleAsCore v)).1 : Real)

/-- Complex polarization of the equation-(2.5) screw-form diagonal. -/
def suzukiEquation25CorePolarized
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) : Complex :=
  (4 : Complex)⁻¹ *
    (suzukiEquation25CoreQuadratic (u + v) -
      suzukiEquation25CoreQuadratic (u - v) -
      Complex.I * suzukiEquation25CoreQuadratic (u + Complex.I • v) +
      Complex.I * suzukiEquation25CoreQuadratic (u - Complex.I • v))

theorem suzukiEquation25CoreQuadratic_eq_normalized
    (hequation25 :
      SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiEquation25CoreQuadratic v =
      (suzukiProjectNormalizedCompleteCoreForm
        (suzukiSmoothCoreLinearSubmoduleAsCore v) : Complex) := by
  unfold suzukiEquation25CoreQuadratic
  exact_mod_cast
    hequation25 suzukiProjectAStar_pos
      (suzukiSmoothCoreLinearSubmoduleAsCore v)

theorem suzukiEquation25CorePolarized_eq_normalized
    (hequation25 :
      SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiEquation25CorePolarized u v =
      suzukiProjectNormalizedCompleteCorePolarizedForm u v := by
  unfold suzukiEquation25CorePolarized
    suzukiProjectNormalizedCompleteCorePolarizedForm
  rw [suzukiEquation25CoreQuadratic_eq_normalized hequation25,
    suzukiEquation25CoreQuadratic_eq_normalized hequation25,
    suzukiEquation25CoreQuadratic_eq_normalized hequation25,
    suzukiEquation25CoreQuadratic_eq_normalized hequation25]

/-- The source-side equation-(2.5) kernel: a limit of explicit screw-form
polarizations along dense smooth-core approximations to the B2S exponential
lifts.  It is not defined by evaluating the completed corrected form. -/
noncomputable def suzukiYoshidaEquation25LimitKernel
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (m n : Int) : Complex :=
  Filter.limUnder atTop fun k =>
    suzukiEquation25CorePolarized
      (suzukiYoshidaCorrectedSmoothCoreApproximation
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m) k)
      (suzukiYoshidaCorrectedSmoothCoreApproximation
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n) k)

theorem suzukiYoshidaCorrectedCompleteForm_tendsto
    {ι : Type*} {l : Filter ι}
    {u v : SuzukiYoshidaCorrectedCommonFormDomain}
    {a b : ι → SuzukiYoshidaCorrectedCommonFormDomain}
    (ha : Tendsto a l (𝓝 u))
    (hb : Tendsto b l (𝓝 v)) :
    Tendsto
      (fun k => suzukiYoshidaCorrectedCompleteForm (a k) (b k))
      l (𝓝 (suzukiYoshidaCorrectedCompleteForm u v)) := by
  have hpair : Tendsto (fun k => (a k, b k)) l (𝓝 (u, v)) :=
    ha.prodMk_nhds hb
  have huncurried :
      Tendsto
        (fun k =>
          Function.uncurry suzukiYoshidaCorrectedCompleteForm
            (a k, b k))
        l
        (𝓝 (Function.uncurry suzukiYoshidaCorrectedCompleteForm (u, v))) :=
    Filter.Tendsto.comp
      suzukiYoshidaCorrectedCompleteForm_jointContinuous.continuousAt
      hpair
  simpa only [Function.uncurry_apply_pair] using huncurried

theorem suzukiEquation25CorePolarized_tendsto_correctedForm
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 :
      SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (m n : Int) :
    Tendsto
      (fun k =>
        suzukiEquation25CorePolarized
          (suzukiYoshidaCorrectedSmoothCoreApproximation
            (suzukiYoshidaExponentialLinearCompletionOfSource
              hsource suzukiProjectAStar_pos m) k)
          (suzukiYoshidaCorrectedSmoothCoreApproximation
            (suzukiYoshidaExponentialLinearCompletionOfSource
              hsource suzukiProjectAStar_pos n) k))
      atTop
      (𝓝 (suzukiYoshidaCorrectedCompleteForm
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n))) := by
  let u :=
    suzukiYoshidaExponentialLinearCompletionOfSource
      hsource suzukiProjectAStar_pos m
  let v :=
    suzukiYoshidaExponentialLinearCompletionOfSource
      hsource suzukiProjectAStar_pos n
  have hu :=
    suzukiYoshidaCorrectedSmoothCoreApproximation_tendsto u
  have hv :=
    suzukiYoshidaCorrectedSmoothCoreApproximation_tendsto v
  have hform :
      Tendsto
        (fun k =>
          suzukiYoshidaCorrectedCompleteForm
            (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
              suzukiProjectAStar
              (suzukiYoshidaCorrectedSmoothCoreApproximation u k))
            (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
              suzukiProjectAStar
              (suzukiYoshidaCorrectedSmoothCoreApproximation v k)))
        atTop (𝓝 (suzukiYoshidaCorrectedCompleteForm u v)) := by
    exact suzukiYoshidaCorrectedCompleteForm_tendsto hu hv
  change
    Tendsto
      (fun k =>
        suzukiEquation25CorePolarized
          (suzukiYoshidaCorrectedSmoothCoreApproximation u k)
          (suzukiYoshidaCorrectedSmoothCoreApproximation v k))
      atTop (𝓝 (suzukiYoshidaCorrectedCompleteForm u v))
  apply hform.congr'
  filter_upwards with k
  exact
    ((suzukiEquation25CorePolarized_eq_normalized hequation25 _ _).trans
      (suzukiYoshidaCorrectedCompleteForm_core_polarized _ _).symm).symm

/-- B2S form-core plus the separate equation-(2.5) source identity identify
the corrected completed exponential pairing with the source-side limit
kernel. -/
theorem suzukiYoshidaCorrectedCompleteForm_exponential_eq_limitKernel
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 :
      SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (m n : Int) :
    suzukiYoshidaCorrectedCompleteForm
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n) =
      suzukiYoshidaEquation25LimitKernel hsource m n := by
  exact
    (suzukiEquation25CorePolarized_tendsto_correctedForm
      hsource hequation25 m n).limUnder_eq.symm

/-- The remaining explicit analytic evaluation in B3Q.  It compares the
source-side equation-(2.5) limit with the independently defined all-integer
DF6D4 formula; neither side is a completed-form evaluation. -/
def SuzukiYoshidaEquation25EndpointKernelEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ m n : Int,
    suzukiYoshidaEquation25LimitKernel hsource m n =
      suzukiYoshidaCorrectedExplicitKernel m n

theorem suzukiYoshidaCorrectedCompleteForm_exponential_eq_explicitKernel
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 :
      SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (hevaluation :
      SuzukiYoshidaEquation25EndpointKernelEvaluation hsource)
    (m n : Int) :
    suzukiYoshidaCorrectedCompleteForm
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n) =
      suzukiYoshidaCorrectedExplicitKernel m n := by
  rw [suzukiYoshidaCorrectedCompleteForm_exponential_eq_limitKernel
    hsource hequation25 m n]
  exact hevaluation m n

end

end RiemannHypothesisProject.Experiments.M100
