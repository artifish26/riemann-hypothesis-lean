import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaComparisonEnergyCoercivity
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaDF0QuarterSineEvaluation
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointFourierL1L2Bridge

/-!
# Ambient Fourier leakage for B3F-E

This module proves the cutoff-44 low-band Fourier estimate on the closed even
and odd Yoshida tails.  It first proves the sharp bound on finite combinations
of high endpoint exponentials from the exact cardinal-sine transform, then
passes to the common closed high-exponential subspace through the continuous
low-band restriction operator.  Both parity tails embed in that closure.
-/

namespace RiemannHypothesisProject.Experiments.M100
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal FourierTransform Topology

def lowBandFourierRestriction :
    SuzukiL2 →L[Complex]
      Lp Complex 2 ((volume : Measure Real).restrict
        (Icc (-suzukiDF6D5B3FEFourierThreshold)
          suzukiDF6D5B3FEFourierThreshold)) :=
  (LpToLpRestrictCLM Real Complex Complex volume 2
    (Icc (-suzukiDF6D5B3FEFourierThreshold)
      suzukiDF6D5B3FEFourierThreshold)).comp
    (MeasureTheory.Lp.fourierTransformₗᵢ Real Complex).toContinuousLinearEquiv.toContinuousLinearMap

theorem lowMass_eq_norm_restriction_sq (v : SuzukiL2) :
    suzukiDF6D5B3FELowFourierMass v =
      ‖lowBandFourierRestriction v‖ ^ 2 := by
  let band := Icc (-suzukiDF6D5B3FEFourierThreshold)
    suzukiDF6D5B3FEFourierThreshold
  let restricted := lowBandFourierRestriction v
  have hmem : MemLp (fun ξ : Real => restricted ξ)
      (2 : ENNReal) ((volume : Measure Real).restrict band) :=
    MeasureTheory.Lp.memLp restricted
  have hself : (inner Complex restricted restricted).re = ‖restricted‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := Complex) restricted
  have hintegrable : Integrable
      (fun ξ : Real => inner Complex (restricted ξ) (restricted ξ))
      ((volume : Measure Real).restrict band) :=
    L2.integrable_inner restricted restricted
  have hnorm : ‖restricted‖ ^ 2 =
      ∫ ξ : Real, ‖restricted ξ‖ ^ 2 ∂((volume : Measure Real).restrict band) := by
    calc
      ‖restricted‖ ^ 2 = (inner Complex restricted restricted).re := hself.symm
      _ = (∫ ξ : Real, inner Complex (restricted ξ) (restricted ξ)
          ∂((volume : Measure Real).restrict band)).re := by
        rw [L2.inner_def]
      _ = ∫ ξ : Real, (inner Complex (restricted ξ) (restricted ξ)).re
          ∂((volume : Measure Real).restrict band) :=
        (integral_re hintegrable).symm
      _ = ∫ ξ : Real, ‖restricted ξ‖ ^ 2
          ∂((volume : Measure Real).restrict band) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ξ => by
          simpa using (inner_self_eq_norm_sq (𝕜 := Complex) (restricted ξ))
  change suzukiDF6D5B3FELowFourierMass v = ‖restricted‖ ^ 2
  rw [hnorm]
  unfold suzukiDF6D5B3FELowFourierMass
  change (∫ ξ in band,
      ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2) = _
  apply integral_congr_ae
  have hcoe := LpToLpRestrictCLM_coeFn Complex band
    (FourierTransform.fourier v : SuzukiL2)
  filter_upwards [hcoe] with ξ hξ
  change ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2 =
    ‖((LpToLpRestrictCLM Real Complex Complex volume 2 band)
      (FourierTransform.fourier v : SuzukiL2)) ξ‖ ^ 2
  rw [hξ]

theorem isClosed_leakage_bound_set (L : Real) :
    IsClosed {v : SuzukiL2 |
      suzukiDF6D5B3FELowFourierMass v ≤ L * ‖v‖ ^ 2} := by
  rw [show {v : SuzukiL2 |
      suzukiDF6D5B3FELowFourierMass v ≤ L * ‖v‖ ^ 2} =
    {v : SuzukiL2 |
      ‖lowBandFourierRestriction v‖ ^ 2 ≤ L * ‖v‖ ^ 2} by
      ext v
      simp only [Set.mem_setOf_eq]
      rw [lowMass_eq_norm_restriction_sq]]
  exact isClosed_le
    ((lowBandFourierRestriction.continuous.norm).pow 2)
    (continuous_const.mul (continuous_norm.pow 2))

theorem fourier_suzukiYoshidaExponentialFunction_eq_cardinal
    {r : Real} (hr : 0 < r) (n : Int) (ξ : Real) :
    FourierTransform.fourier (suzukiYoshidaExponentialFunction r n) ξ =
      ((Real.sqrt (2 * r) *
        Real.sinc (Real.pi * (2 * r * ξ - (n : Real))) : Real) : Complex) := by
  by_cases hξ : ξ = (n : Real) / (2 * r)
  · rw [hξ, fourier_suzukiYoshidaExponentialFunction_resonant hr]
    have hr0 : r ≠ 0 := hr.ne'
    field_simp [hr0]
    simp
  · rw [fourier_suzukiYoshidaExponentialFunction_nonresonant hr n ξ hξ]
    have harg : Real.pi * (2 * r * ξ - (n : Real)) ≠ 0 := by
      apply mul_ne_zero Real.pi_ne_zero
      intro h
      apply hξ
      field_simp [hr.ne'] at h ⊢
      linarith
    rw [Real.sinc_of_ne_zero harg]
    unfold suzukiYoshidaEndpointFourierDetuning
    norm_cast
    have hsqrt : Real.sqrt (2 * r) ≠ 0 := by positivity
    field_simp [hr.ne', Real.pi_ne_zero, hsqrt]
    rw [show Real.pi * ((n : Real) - 2 * r * ξ) =
        -(Real.pi * (2 * r * ξ - (n : Real))) by ring,
      Real.sin_neg]
    have hsquare : Real.sqrt (2 * r) ^ 2 = 2 * r :=
      Real.sq_sqrt (by positivity)
    rw [hsquare]
    have hdelta : 2 * r * ξ - (n : Real) ≠ 0 :=
      fun h => harg (mul_eq_zero.mpr (Or.inr h))
    have hdeltaNeg : (n : Real) - 2 * r * ξ ≠ 0 := by
      intro h
      apply hdelta
      linarith
    field_simp [hdelta, hdeltaNeg]
    ring

abbrev Cutoff44HighIndex :=
  {n : Int // n ∉ Finset.Icc (-44 : Int) 44}

def cutoff44HighExponential (j : Cutoff44HighIndex) : SuzukiL2 :=
  suzukiYoshidaExponentialL2 suzukiProjectAStar
    suzukiProjectAStar_pos (-j.1)

theorem orthonormal_cutoff44HighExponential :
    Orthonormal Complex cutoff44HighExponential := by
  unfold cutoff44HighExponential
  apply (orthonormal_suzukiYoshidaExponentialL2
    suzukiProjectAStar_pos).comp
  intro i j h
  exact Subtype.ext (neg_injective h)

theorem fourier_cutoff44HighExponential_coe_ae
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (j : Cutoff44HighIndex) :
    ((FourierTransform.fourier (cutoff44HighExponential j) : SuzukiL2) :
      Real → Complex) =ᵐ[volume]
      fun ξ => ((Real.sqrt (2 * suzukiProjectAStar) *
        Real.sinc (Real.pi *
          (2 * suzukiProjectAStar * ξ + (j.1 : Real))) : Real) : Complex) := by
  unfold cutoff44HighExponential
  filter_upwards [fourier_suzukiYoshidaExponentialL2_coe_ae
    hsource suzukiProjectAStar_pos (-j.1)] with ξ hξ
  rw [hξ, fourier_suzukiYoshidaExponentialFunction_eq_cardinal
    suzukiProjectAStar_pos]
  push_cast
  ring_nf

theorem cardinalSineCutoff44TailDensity_eq_tsum_high (x : Real) :
    cardinalSineCutoff44TailDensity x =
      ∑' j : Cutoff44HighIndex,
        Real.sinc (Real.pi * (x + (j.1 : Real))) ^ 2 := by
  have hs := summable_sq_sinc_pi_mul_add_int x
  have hsplit := hs.sum_add_tsum_subtype_compl
    (Finset.Icc (-44 : Int) 44)
  rw [tsum_sq_sinc_pi_mul_add_int] at hsplit
  unfold cardinalSineCutoff44TailDensity cardinalSineCutoff44LowDensity
  linarith

theorem norm_finset_sum_mul_sq_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c z : ι → Complex) :
    ‖∑ i ∈ s, c i * z i‖ ^ 2 ≤
      (∑ i ∈ s, ‖c i‖ ^ 2) * (∑ i ∈ s, ‖z i‖ ^ 2) := by
  calc
    ‖∑ i ∈ s, c i * z i‖ ^ 2 ≤
        (∑ i ∈ s, ‖c i * z i‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ = (∑ i ∈ s, ‖c i‖ * ‖z i‖) ^ 2 := by
      simp_rw [norm_mul]
    _ ≤ (∑ i ∈ s, ‖c i‖ ^ 2) * (∑ i ∈ s, ‖z i‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖c i‖) (fun i => ‖z i‖)

theorem norm_sq_cutoff44HighExponential_linearCombination
    (l : Cutoff44HighIndex →₀ Complex) :
    ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ ^ 2 =
      l.sum fun _ c => ‖c‖ ^ 2 := by
  let v := Finsupp.linearCombination Complex cutoff44HighExponential l
  have hinner := orthonormal_cutoff44HighExponential.inner_finsupp_eq_sum_left l l
  have hself : (inner Complex v v).re = ‖v‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := Complex) v
  change inner Complex v v = _ at hinner
  rw [hinner] at hself
  rw [← hself]
  change (∑ i ∈ l.support,
      ((starRingEnd Complex) (l i) * l i)).re =
    ∑ i ∈ l.support, ‖l i‖ ^ 2
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    neg_mul, sub_neg_eq_add]
  exact (Complex.sq_norm (l i)).symm

theorem fourier_cutoff44HighExponential_linearCombination_coe_ae
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (l : Cutoff44HighIndex →₀ Complex) :
    ((FourierTransform.fourier
      (Finsupp.linearCombination Complex cutoff44HighExponential l) :
        SuzukiL2) : Real → Complex) =ᵐ[volume]
      fun ξ => ∑ j ∈ l.support,
        l j * ((Real.sqrt (2 * suzukiProjectAStar) *
          Real.sinc (Real.pi *
            (2 * suzukiProjectAStar * ξ + (j.1 : Real))) : Real) : Complex) := by
  have hL2 : FourierTransform.fourier
      (Finsupp.linearCombination Complex cutoff44HighExponential l) =
      ∑ j ∈ l.support, l j •
        FourierTransform.fourier (cutoff44HighExponential j) := by
    rw [Finsupp.linearCombination_apply]
    change FourierTransform.fourier
      (∑ j ∈ l.support, l j • cutoff44HighExponential j) = _
    induction l.support using Finset.induction_on with
    | empty => simp [FourierTransform.fourier_zero]
    | @insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj,
          FourierTransform.fourier_add,
          FourierTransform.fourier_smul, ih]
  rw [hL2]
  have hsum := MeasureTheory.Lp.coeFn_finsetSum l.support
    (fun j => l j •
      (FourierTransform.fourier (cutoff44HighExponential j) : SuzukiL2))
  have hsmul : ∀ᵐ ξ ∂(volume : Measure Real), ∀ j,
      ((l j • FourierTransform.fourier
        (cutoff44HighExponential j) : SuzukiL2) ξ) =
        l j * ((FourierTransform.fourier
          (cutoff44HighExponential j) : SuzukiL2) ξ) := by
    apply ae_all_iff.mpr
    intro j
    exact MeasureTheory.Lp.coeFn_smul (l j)
      (FourierTransform.fourier (cutoff44HighExponential j) : SuzukiL2)
  have hmodes : ∀ᵐ ξ ∂(volume : Measure Real), ∀ j,
      ((FourierTransform.fourier
        (cutoff44HighExponential j) : SuzukiL2) ξ) =
      ((Real.sqrt (2 * suzukiProjectAStar) *
        Real.sinc (Real.pi *
          (2 * suzukiProjectAStar * ξ + (j.1 : Real))) : Real) : Complex) := by
    apply ae_all_iff.mpr
    intro j
    exact fourier_cutoff44HighExponential_coe_ae hsource j
  filter_upwards [hsum, hsmul, hmodes] with ξ hsumξ hsmulξ hmodesξ
  rw [hsumξ]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hsmulξ j, hmodesξ j]

theorem continuous_cardinalSineCutoff44TailDensity :
    Continuous cardinalSineCutoff44TailDensity := by
  unfold cardinalSineCutoff44TailDensity cardinalSineCutoff44LowDensity
  fun_prop

theorem integral_scaled_cardinalSineCutoff44TailDensity :
    (∫ ξ in -suzukiDF6D5B3FEFourierThreshold..
        suzukiDF6D5B3FEFourierThreshold,
      (2 * suzukiProjectAStar) *
        cardinalSineCutoff44TailDensity
          ((2 * suzukiProjectAStar) * ξ)) =
      cardinalSineCutoff44Leakage := by
  have ha : 2 * suzukiProjectAStar ≠ 0 :=
    mul_ne_zero (by norm_num) suzukiProjectAStar_pos.ne'
  rw [intervalIntegral.integral_const_mul]
  change (2 * suzukiProjectAStar) •
      (∫ ξ in -suzukiDF6D5B3FEFourierThreshold..
        suzukiDF6D5B3FEFourierThreshold,
        cardinalSineCutoff44TailDensity
          ((2 * suzukiProjectAStar) * ξ)) = _
  rw [intervalIntegral.smul_integral_comp_mul_left
    cardinalSineCutoff44TailDensity (2 * suzukiProjectAStar)]
  unfold cardinalSineCutoff44Leakage cardinalSineCutoff44Window
    suzukiDF6D5B3FEFourierThreshold
  congr 1 <;> field_simp [ha, suzukiProjectAStar_pos.ne']

theorem cutoff44HighExponential_linearCombination_leakage
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (l : Cutoff44HighIndex →₀ Complex) :
    suzukiDF6D5B3FELowFourierMass
        (Finsupp.linearCombination Complex cutoff44HighExponential l) ≤
      cardinalSineCutoff44Leakage *
        ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ ^ 2 := by
  let v := Finsupp.linearCombination Complex cutoff44HighExponential l
  let coeffSq : Real := l.sum fun _ c => ‖c‖ ^ 2
  have hcoeff : 0 ≤ coeffSq := by
    unfold coeffSq
    exact Finsupp.sum_nonneg fun _ _ => sq_nonneg _
  have hfourier :=
    fourier_cutoff44HighExponential_linearCombination_coe_ae hsource l
  have hpoint : ∀ᵐ ξ ∂(volume : Measure Real),
      ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2 ≤
        coeffSq * ((2 * suzukiProjectAStar) *
          cardinalSineCutoff44TailDensity
            ((2 * suzukiProjectAStar) * ξ)) := by
    filter_upwards [hfourier] with ξ hξ
    rw [hξ]
    have hcs := norm_finset_sum_mul_sq_le l.support
      (fun j => l j)
      (fun j => ((Real.sqrt (2 * suzukiProjectAStar) *
        Real.sinc (Real.pi *
          (2 * suzukiProjectAStar * ξ + (j.1 : Real))) : Real) : Complex))
    apply hcs.trans
    rw [cardinalSineCutoff44TailDensity_eq_tsum_high]
    have hsqrt : Real.sqrt (2 * suzukiProjectAStar) ^ 2 =
        2 * suzukiProjectAStar := Real.sq_sqrt
          (mul_nonneg (by norm_num) suzukiProjectAStar_pos.le)
    have hsummable : Summable (fun j : Cutoff44HighIndex =>
        Real.sinc (Real.pi *
          (2 * suzukiProjectAStar * ξ + (j.1 : Real))) ^ 2) :=
      (summable_sq_sinc_pi_mul_add_int
        (2 * suzukiProjectAStar * ξ)).subtype _
    have hsum := hsummable.sum_le_tsum l.support
      (fun j hj => sq_nonneg _)
    have hzEq :
        (∑ i ∈ l.support,
          ‖((Real.sqrt (2 * suzukiProjectAStar) *
            Real.sinc (Real.pi *
              (2 * suzukiProjectAStar * ξ + (i.1 : Real))) : Real) :
                Complex)‖ ^ 2) =
          (2 * suzukiProjectAStar) *
            ∑ i ∈ l.support, Real.sinc (Real.pi *
              (2 * suzukiProjectAStar * ξ + (i.1 : Real))) ^ 2 := by
      simp_rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hsqrt]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [sq_abs]
    rw [hzEq]
    change coeffSq * ((2 * suzukiProjectAStar) *
        ∑ i ∈ l.support, Real.sinc (Real.pi *
          (2 * suzukiProjectAStar * ξ + (i.1 : Real))) ^ 2) ≤
      coeffSq * ((2 * suzukiProjectAStar) *
        ∑' j : Cutoff44HighIndex, Real.sinc (Real.pi *
          (2 * suzukiProjectAStar * ξ + (j.1 : Real))) ^ 2)
    apply mul_le_mul_of_nonneg_left _ hcoeff
    exact mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (by norm_num) suzukiProjectAStar_pos.le)
  have hrightIntegrable : IntervalIntegrable
      (fun ξ : Real => coeffSq * ((2 * suzukiProjectAStar) *
        cardinalSineCutoff44TailDensity
          ((2 * suzukiProjectAStar) * ξ))) volume
      (-suzukiDF6D5B3FEFourierThreshold)
      suzukiDF6D5B3FEFourierThreshold := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (continuous_const.mul
      (continuous_cardinalSineCutoff44TailDensity.comp
        (continuous_const.mul continuous_id)))
  have hleftIntegrable : IntervalIntegrable
      (fun ξ : Real => ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2)
      volume (-suzukiDF6D5B3FEFourierThreshold)
      suzukiDF6D5B3FEFourierThreshold :=
    (integrable_suzukiDF6D5B3FE_fourierNormSq v).intervalIntegrable
  have hthresholdNonneg : 0 ≤ suzukiDF6D5B3FEFourierThreshold :=
    (by linarith [suzukiDF6D5B3FE_fourierThreshold_one_le])
  have hmono := intervalIntegral.integral_mono_ae
    (neg_le_self hthresholdNonneg) hleftIntegrable hrightIntegrable hpoint
  rw [intervalIntegral.integral_const_mul,
    integral_scaled_cardinalSineCutoff44TailDensity] at hmono
  calc
    suzukiDF6D5B3FELowFourierMass
        (Finsupp.linearCombination Complex cutoff44HighExponential l) =
        ∫ ξ in -suzukiDF6D5B3FEFourierThreshold..
          suzukiDF6D5B3FEFourierThreshold,
          ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2 := by
      unfold suzukiDF6D5B3FELowFourierMass
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le
          (by linarith [suzukiDF6D5B3FE_fourierThreshold_one_le])]
    _ ≤ cardinalSineCutoff44Leakage * coeffSq := by
      simpa [mul_comm] using hmono
    _ = cardinalSineCutoff44Leakage *
        ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ ^ 2 := by
      rw [norm_sq_cutoff44HighExponential_linearCombination]

def cutoff44HighExponentialSubspace : Submodule Complex SuzukiL2 :=
  Submodule.span Complex (Set.range cutoff44HighExponential)

theorem cutoff44HighExponentialClosure_leakage
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    {v : SuzukiL2}
    (hv : v ∈ cutoff44HighExponentialSubspace.topologicalClosure) :
    suzukiDF6D5B3FELowFourierMass v ≤
      cardinalSineCutoff44Leakage * ‖v‖ ^ 2 := by
  let P : Set SuzukiL2 := {w : SuzukiL2 |
    suzukiDF6D5B3FELowFourierMass w ≤
      cardinalSineCutoff44Leakage * ‖w‖ ^ 2}
  have hKP : cutoff44HighExponentialSubspace ≤ P := by
    intro w hw
    unfold cutoff44HighExponentialSubspace at hw
    obtain ⟨l, rfl⟩ :=
      Finsupp.mem_span_range_iff_exists_finsupp.mp hw
    exact cutoff44HighExponential_linearCombination_leakage hsource l
  have hclosure : closure (cutoff44HighExponentialSubspace : Set SuzukiL2) ⊆ P :=
    closure_minimal hKP
      (isClosed_leakage_bound_set cardinalSineCutoff44Leakage)
  apply hclosure
  rw [← Submodule.topologicalClosure_coe]
  exact hv

theorem suzukiYoshidaExponentialL2_mem_cutoff44HighExponentialSubspace
    (m : Int) (hm : m ∉ Finset.Icc (-44 : Int) 44) :
    suzukiYoshidaExponentialL2 suzukiProjectAStar
        suzukiProjectAStar_pos m ∈ cutoff44HighExponentialSubspace := by
  have hneg : -m ∉ Finset.Icc (-44 : Int) 44 := by
    simp only [Finset.mem_Icc, not_and_or] at hm ⊢
    omega
  let j : Cutoff44HighIndex := ⟨-m, hneg⟩
  have hj : cutoff44HighExponential j ∈
      Submodule.span Complex (Set.range cutoff44HighExponential) :=
    Submodule.subset_span (Set.mem_range_self j)
  change cutoff44HighExponential j ∈ cutoff44HighExponentialSubspace at hj
  simpa [cutoff44HighExponential, j] using hj

theorem suzukiYoshidaEvenL2_mem_cutoff44HighExponentialSubspace
    (n : {n : Nat // 45 ≤ n}) :
    suzukiYoshidaEvenL2 suzukiProjectAStar
        suzukiProjectAStar_pos n.1 ∈ cutoff44HighExponentialSubspace := by
  have hn0 : n.1 ≠ 0 := by omega
  have hnInt : (45 : Int) ≤ (n.1 : Int) := by exact_mod_cast n.2
  have hpos : (n.1 : Int) ∉ Finset.Icc (-44 : Int) 44 := by
    simp only [Finset.mem_Icc, not_and_or]
    right
    omega
  have hneg : -(n.1 : Int) ∉ Finset.Icc (-44 : Int) 44 := by
    simp only [Finset.mem_Icc, not_and_or]
    left
    omega
  unfold suzukiYoshidaEvenL2
  rw [dif_neg hn0]
  exact cutoff44HighExponentialSubspace.smul_mem _
    (cutoff44HighExponentialSubspace.add_mem
      (suzukiYoshidaExponentialL2_mem_cutoff44HighExponentialSubspace _ hpos)
      (suzukiYoshidaExponentialL2_mem_cutoff44HighExponentialSubspace _ hneg))

theorem suzukiYoshidaOddL2_mem_cutoff44HighExponentialSubspace
    (n : {n : Nat // 45 ≤ n}) :
    suzukiYoshidaOddL2 suzukiProjectAStar
        suzukiProjectAStar_pos n.1 ∈ cutoff44HighExponentialSubspace := by
  have hnInt : (45 : Int) ≤ (n.1 : Int) := by exact_mod_cast n.2
  have hpos : (n.1 : Int) ∉ Finset.Icc (-44 : Int) 44 := by
    simp only [Finset.mem_Icc, not_and_or]
    right
    omega
  have hneg : -(n.1 : Int) ∉ Finset.Icc (-44 : Int) 44 := by
    simp only [Finset.mem_Icc, not_and_or]
    left
    omega
  unfold suzukiYoshidaOddL2
  exact cutoff44HighExponentialSubspace.smul_mem _
    (cutoff44HighExponentialSubspace.sub_mem
      (suzukiYoshidaExponentialL2_mem_cutoff44HighExponentialSubspace _ hpos)
      (suzukiYoshidaExponentialL2_mem_cutoff44HighExponentialSubspace _ hneg))

theorem suzukiDF6D5B3TEvenAmbientFarSubspace_le_cutoff44HighClosure :
    suzukiDF6D5B3TEvenAmbientFarSubspace ≤
      cutoff44HighExponentialSubspace.topologicalClosure := by
  unfold suzukiDF6D5B3TEvenAmbientFarSubspace
  apply Submodule.topologicalClosure_minimal
  · rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    exact cutoff44HighExponentialSubspace.le_topologicalClosure
      (suzukiYoshidaEvenL2_mem_cutoff44HighExponentialSubspace n)
  · exact cutoff44HighExponentialSubspace.isClosed_topologicalClosure

theorem suzukiDF6D5B3TOddAmbientFarSubspace_le_cutoff44HighClosure :
    suzukiDF6D5B3TOddAmbientFarSubspace ≤
      cutoff44HighExponentialSubspace.topologicalClosure := by
  unfold suzukiDF6D5B3TOddAmbientFarSubspace
  apply Submodule.topologicalClosure_minimal
  · rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    exact cutoff44HighExponentialSubspace.le_topologicalClosure
      (suzukiYoshidaOddL2_mem_cutoff44HighExponentialSubspace n)
  · exact cutoff44HighExponentialSubspace.isClosed_topologicalClosure

theorem suzukiDF6D5B3FEAmbientFourierLeakage_of_source
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiDF6D5B3FEAmbientFourierLeakage := by
  intro v hv
  rw [← cardinalSineCutoff44Leakage_eq_suzukiDF6D4DF0LeakageFraction_proved]
  apply cutoff44HighExponentialClosure_leakage hsource
  rcases hv with heven | hodd
  · exact suzukiDF6D5B3TEvenAmbientFarSubspace_le_cutoff44HighClosure heven
  · exact suzukiDF6D5B3TOddAmbientFarSubspace_le_cutoff44HighClosure hodd

end
end RiemannHypothesisProject.Experiments.M100
