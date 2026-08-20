import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCorrectedForms
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCardinalSinePartition
import RiemannHypothesisProject.Experiments.M100.SuzukiLowFrequencyCompletionIdentification

/-!
# Comparison-energy coercivity for M100-DF6D5B3F-E

This module freezes the exact sharp comparison-energy theorem family consumed
by B3F-E.  The hard analytic input remains visible on the matching even and
odd parity-far completion subtypes constructed by B3T.  The elementary
consequences derive the uniform coefficient `5`, the reciprocal coefficient
`1/5`, and the existing B3T physical-`L²` far-coercivity targets.

No density statement is upgraded to surjectivity, and no graph norm is used
in place of the physical `L²` norm.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

/-- B3V's corrected comparison form bundled for the B3T receiving surfaces. -/
def suzukiYoshidaComparisonHermitianForm :
    SuzukiDF6D5B3THermitianForm where
  toFun := suzukiYoshidaComparisonForm
  conj_symm := suzukiYoshidaComparisonForm_conj_symm

/-! ## Fourier-mass decomposition of the sharp source theorem -/

/-- The ordinary-Fourier cutoff corresponding to `U = 97/4` in the DF0
cardinal-sine calculation.  Mathlib's Fourier variable is the paper variable
divided by `2 * pi`, hence the factor `2 * suzukiProjectAStar`. -/
def suzukiDF6D5B3FEFourierThreshold : Real :=
  (97 / 4 : Real) / (2 * suzukiProjectAStar)

theorem suzukiDF6D4DF0ZeroCrossing_pos :
    0 < suzukiDF6D4DF0ZeroCrossing := by
  have hz := suzukiDF6D4DF0ZeroCrossingInterval_contains.1
  have hgrid : (0 : Rat) < suzukiDF6D4DF0ZeroCrossingInterval.lower := by
    native_decide
  have hgridReal :
      (0 : Real) < (suzukiDF6D4DF0ZeroCrossingInterval.lower : Real) := by
    exact_mod_cast hgrid
  exact hgridReal.trans_le hz

theorem suzukiDF6D4DF0ZeroCrossing_lt_45 :
    suzukiDF6D4DF0ZeroCrossing < 45 := by
  have hz := suzukiDF6D4DF0ZeroCrossingInterval_contains.2
  have hgrid : suzukiDF6D4DF0ZeroCrossingInterval.upper < (45 : Rat) := by
    native_decide
  exact hz.trans_lt (by exact_mod_cast hgrid)

/-- The physical-frequency zero crossing of Suzuki's normalized source
multiplier.  Under `u = 2 * a * ξ`, this is exactly the DF0 dimensionless
zero crossing. -/
def suzukiDF6D5B3FENegativeWeightThreshold : Real :=
  suzukiDF6D4DF0ZeroCrossing / (2 * suzukiProjectAStar)

theorem suzukiDF6D5B3FENegativeWeightThreshold_pos :
    0 < suzukiDF6D5B3FENegativeWeightThreshold := by
  unfold suzukiDF6D5B3FENegativeWeightThreshold
  exact div_pos suzukiDF6D4DF0ZeroCrossing_pos
    (mul_pos (by norm_num) suzukiProjectAStar_pos)

theorem suzukiDF6D5B3FE_twoA_mul_negativeWeightThreshold :
    (2 * suzukiProjectAStar) *
        suzukiDF6D5B3FENegativeWeightThreshold =
      suzukiDF6D4DF0ZeroCrossing := by
  unfold suzukiDF6D5B3FENegativeWeightThreshold
  field_simp [suzukiProjectAStar_pos.ne']

/-- The nonnegative part of the normalized source multiplier below its zero
crossing, expressed in the project dimensionless coordinate. -/
def suzukiDF6D5B3FENormalizedNegativeWeight (ξ : Real) : Real :=
  Real.log (suzukiDF6D4DF0ZeroCrossing /
    |(2 * suzukiProjectAStar) * ξ|)

/-- Physical Fourier energy carried by the negative part of Suzuki's
normalized multiplier. -/
def suzukiDF6D5B3FENormalizedNegativeWeightEnergy (v : SuzukiL2) : Real :=
  ∫ ξ in -suzukiDF6D5B3FENegativeWeightThreshold..
      suzukiDF6D5B3FENegativeWeightThreshold,
    suzukiDF6D5B3FENormalizedNegativeWeight ξ *
      ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2

/-- Fourier mass in the symmetric DF0 low band.  This is well-defined on an
`L²` class because the integral only depends on its almost-everywhere
representative. -/
def suzukiDF6D5B3FELowFourierMass (v : SuzukiL2) : Real :=
  ∫ ξ in Icc (-suzukiDF6D5B3FEFourierThreshold)
      suzukiDF6D5B3FEFourierThreshold,
    ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2

/-- The second, logarithmically weighted coordinate of the Hilbert graph. -/
def suzukiDF6D5B3FELogWeightedCoordinate
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) : SuzukiL2 :=
  v.1.1.snd

/-- The Hilbert graph norm splits into its physical and logarithmically
weighted Fourier coordinates. -/
theorem suzukiDF6D5B3FE_graph_norm_sq_split
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    ‖v‖ ^ 2 = ‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 +
      ‖suzukiDF6D5B3FELogWeightedCoordinate v‖ ^ 2 := by
  change ‖v.1.1‖ ^ 2 = ‖v.1.1.fst‖ ^ 2 + ‖v.1.1.snd‖ ^ 2
  exact WithLp.prod_norm_sq_eq_of_L2 v.1.1

/-- The second graph coordinate is represented by the square root of the
positive logarithmic weight times the ordinary `L²` Fourier transform of the
physical coordinate. -/
theorem suzukiDF6D5B3FE_logWeightedCoordinate_coe_ae
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    ((suzukiDF6D5B3FELogWeightedCoordinate v : SuzukiL2) :
        Real → Complex) =ᵐ[volume]
      fun ξ =>
        ((Real.sqrt (suzukiLogFourierWeight ξ) : Real) : Complex) *
          ((FourierTransform.fourier
            (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ) := by
  have hgraph :
      (WithLp.linearEquiv 2 Complex (SuzukiL2 × SuzukiL2)) v.1.1 ∈
        suzukiLogFourierPMap.graph := by
    exact v.1.2
  rw [LinearPMap.mem_graph_iff] at hgraph
  obtain ⟨w, hwPhysical, hwWeighted⟩ := hgraph
  change (w : SuzukiL2) = v.1.1.fst at hwPhysical
  change suzukiLogWeightedFourierToL2 w = v.1.1.snd at hwWeighted
  have hcoe := suzukiLogWeightedFourierToL2_coe_ae w
  change ((v.1.1.snd : SuzukiL2) : Real → Complex) =ᵐ[volume] _
  rw [← hwWeighted]
  filter_upwards [hcoe] with ξ hξ
  rw [hξ]
  unfold suzukiLogWeightedFourier
  rw [hwPhysical]
  rfl

theorem integrable_suzukiDF6D5B3FE_fourierNormSq (v : SuzukiL2) :
    Integrable (fun ξ : Real =>
      ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2) := by
  exact (MeasureTheory.Lp.memLp
    (FourierTransform.fourier v : SuzukiL2)).integrable_norm_pow
      (by norm_num)

theorem suzukiDF6D5B3FE_lowFourierMass_nonneg (v : SuzukiL2) :
    0 ≤ suzukiDF6D5B3FELowFourierMass v := by
  unfold suzukiDF6D5B3FELowFourierMass
  exact integral_nonneg fun ξ => sq_nonneg _

/-- Plancherel normalization for the Fourier density used by B3F-E. -/
theorem suzukiDF6D5B3FE_integral_fourierNormSq (v : SuzukiL2) :
    (∫ ξ : Real, ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2) =
      ‖v‖ ^ 2 := by
  let transformed : SuzukiL2 := FourierTransform.fourier v
  have hmem : MemLp (fun ξ : Real => transformed ξ)
      (2 : ENNReal) volume := MeasureTheory.Lp.memLp transformed
  have hnorm := norm_sq_toLp_eq_integral_norm_sq
    (fun ξ : Real => transformed ξ) hmem
  rw [MeasureTheory.Lp.toLp_coeFn transformed hmem] at hnorm
  calc
    (∫ ξ : Real, ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2) =
        ‖transformed‖ ^ 2 := by
      simpa only [transformed] using hnorm.symm
    _ = ‖v‖ ^ 2 := by
      rw [MeasureTheory.Lp.norm_fourier_eq]

/-- Positivity of the certified high-band multiplier. -/
theorem suzukiDF6D4DF0HighWeight_nonneg :
    0 ≤ suzukiDF6D4DF0HighWeight := by
  have hcontains := suzukiDF6D4DF0HighWeightInterval_contains.1
  have hgrid :
      (0 : Rat) ≤ suzukiDF6D4DF0HighWeightInterval.lower := by
    native_decide
  have hgridReal :
      (0 : Real) ≤ (suzukiDF6D4DF0HighWeightInterval.lower : Real) := by
    exact_mod_cast hgrid
  exact hgridReal.trans hcontains

theorem suzukiSourceLogNormalizationConstant_nonneg :
    0 ≤ suzukiSourceLogNormalizationConstant := by
  rw [suzukiSourceLogNormalizationConstant_eq_df0Scalar]
  have hcontains := suzukiDF6D4DF0ScalarInterval_contains.1
  have hgrid : (0 : Rat) ≤ suzukiDF6D4DF0ScalarInterval.lower := by
    native_decide
  have hgridReal :
      (0 : Real) ≤ (suzukiDF6D4DF0ScalarInterval.lower : Real) := by
    exact_mod_cast hgrid
  exact hgridReal.trans hcontains

theorem suzukiDF6D5B3FE_fourierThreshold_one_le :
    1 ≤ suzukiDF6D5B3FEFourierThreshold := by
  have haUpper := fineAStarInterval_contains.2
  have haPositive : 0 < 2 * suzukiProjectAStar := by
    exact mul_pos (by norm_num) suzukiProjectAStar_pos
  rw [suzukiDF6D5B3FEFourierThreshold, le_div_iff₀ haPositive]
  norm_num [fineAStarInterval] at haUpper ⊢
  linarith

theorem suzukiDF6D5B3FE_highWeight_identity :
    Real.log suzukiDF6D5B3FEFourierThreshold +
        suzukiSourceLogNormalizationConstant =
      suzukiDF6D4DF0HighWeight := by
  have ha : suzukiProjectAStar ≠ 0 := suzukiProjectAStar_pos.ne'
  have htwoA : 2 * suzukiProjectAStar ≠ 0 := mul_ne_zero (by norm_num) ha
  unfold suzukiDF6D5B3FEFourierThreshold
    suzukiSourceLogNormalizationConstant suzukiDF6D4DF0HighWeight
  rw [Real.log_div (by norm_num : (97 / 4 : Real) ≠ 0) htwoA,
    Real.log_mul (by norm_num : (2 : Real) ≠ 0) ha,
    Real.log_mul (by norm_num : (2 : Real) ≠ 0) Real.pi_ne_zero]
  ring

/-- Above the DF0 Fourier cutoff, the positive graph multiplier plus its
source normalization is bounded below by the certified high weight. -/
theorem suzukiDF6D5B3FE_highWeight_le_graphWeight_add_normalization
    {ξ : Real}
    (hξ : ξ ∈ (Icc (-suzukiDF6D5B3FEFourierThreshold)
      suzukiDF6D5B3FEFourierThreshold)ᶜ) :
    suzukiDF6D4DF0HighWeight ≤
      suzukiLogFourierWeight ξ +
        (suzukiSourceLogNormalizationConstant - 1) := by
  have habs : suzukiDF6D5B3FEFourierThreshold ≤ |ξ| := by
    have hnot : ¬ (-suzukiDF6D5B3FEFourierThreshold ≤ ξ ∧
        ξ ≤ suzukiDF6D5B3FEFourierThreshold) := by
      simpa only [mem_compl_iff, mem_Icc] using hξ
    by_cases hleft : ξ < -suzukiDF6D5B3FEFourierThreshold
    · exact le_trans (by linarith) (neg_le_abs ξ)
    · have hleft' : -suzukiDF6D5B3FEFourierThreshold ≤ ξ :=
        le_of_not_gt hleft
      have hright : suzukiDF6D5B3FEFourierThreshold < ξ := by
        by_contra hright
        exact hnot ⟨hleft', le_of_not_gt hright⟩
      exact le_trans hright.le (le_abs_self ξ)
  have habsOne : 1 ≤ |ξ| :=
    suzukiDF6D5B3FE_fourierThreshold_one_le.trans habs
  have hlog := Real.log_le_log
    (lt_of_lt_of_le zero_lt_one
      suzukiDF6D5B3FE_fourierThreshold_one_le) habs
  rw [suzukiDF6D5B3FE_highWeight_identity.symm]
  unfold suzukiLogFourierWeight
  rw [Real.posLog_eq_log]
  · linarith
  · simpa only [abs_abs] using habsOne

/-- The nonnegative positive-source multiplier used before subtracting the
low-frequency logarithmic loss. -/
theorem suzukiDF6D5B3FE_graphWeight_add_normalization_nonneg (ξ : Real) :
    0 ≤ suzukiLogFourierWeight ξ +
      (suzukiSourceLogNormalizationConstant - 1) := by
  have hweight := suzukiLogFourierWeight_one_le ξ
  linarith [suzukiSourceLogNormalizationConstant_nonneg]

/-- Integral realization of the second Hilbert-graph coordinate for an
arbitrary completed element. -/
theorem suzukiDF6D5B3FE_logWeightedCoordinate_norm_sq
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    ‖suzukiDF6D5B3FELogWeightedCoordinate v‖ ^ 2 =
      ∫ ξ : Real, suzukiLogFourierWeight ξ *
        ‖(FourierTransform.fourier
          (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ‖ ^ 2 := by
  let weighted := suzukiDF6D5B3FELogWeightedCoordinate v
  have hmem : MemLp (fun ξ : Real => weighted ξ)
      (2 : ENNReal) volume := MeasureTheory.Lp.memLp weighted
  have hnorm := norm_sq_toLp_eq_integral_norm_sq
    (fun ξ : Real => weighted ξ) hmem
  rw [MeasureTheory.Lp.toLp_coeFn weighted hmem] at hnorm
  calc
    ‖suzukiDF6D5B3FELogWeightedCoordinate v‖ ^ 2 =
        ∫ ξ : Real, ‖weighted ξ‖ ^ 2 := by
      simpa only [weighted] using hnorm
    _ = ∫ ξ : Real, suzukiLogFourierWeight ξ *
          ‖(FourierTransform.fourier
            (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [suzukiDF6D5B3FE_logWeightedCoordinate_coe_ae v]
        with ξ hξ
      dsimp only [weighted]
      rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt (suzukiLogFourierWeight_nonneg ξ)]

theorem integrable_suzukiDF6D5B3FE_graphWeight_fourierNormSq
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    Integrable (fun ξ : Real => suzukiLogFourierWeight ξ *
      ‖(FourierTransform.fourier
        (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ‖ ^ 2) := by
  let weighted := suzukiDF6D5B3FELogWeightedCoordinate v
  have hnorm : Integrable (fun ξ : Real => ‖weighted ξ‖ ^ 2) :=
    (MeasureTheory.Lp.memLp weighted).integrable_norm_pow (by norm_num)
  apply hnorm.congr
  filter_upwards [suzukiDF6D5B3FE_logWeightedCoordinate_coe_ae v]
    with ξ hξ
  dsimp only [weighted]
  rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (suzukiLogFourierWeight_nonneg ξ)]

/-- Adding back the low-frequency loss leaves exactly the positive graph
multiplier plus the fixed source normalization. -/
theorem suzukiDF6D5B3FE_comparison_add_loss_self_re
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    (suzukiYoshidaComparisonForm v v).re +
        (suzukiLowFrequencyLogLossEnergy
          suzukiProjectAStar_pos v v).re =
      ‖suzukiDF6D5B3FELogWeightedCoordinate v‖ ^ 2 +
        (suzukiSourceLogNormalizationConstant - 1) *
          ‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 := by
  have hself : (inner Complex v v).re = ‖v‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := Complex) v
  have hphysical :
      (inner Complex
        (suzukiLogRadiusLinearCompletionToL2 v)
        (suzukiLogRadiusLinearCompletionToL2 v)).re =
          ‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := Complex) _
  unfold suzukiYoshidaComparisonForm
  rw [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    hself, hphysical, suzukiDF6D5B3FE_graph_norm_sq_split]
  ring

/-- The high-band estimate is an elementary consequence of the completed
graph representation and the cutoff multiplier inequality.  It holds on the
entire common form domain; no parity or high-mode hypothesis is used here. -/
theorem suzukiDF6D5B3FE_rawGraphLoss_highBandEnergyLower
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    suzukiDF6D4DF0HighWeight *
        (‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 -
          suzukiDF6D5B3FELowFourierMass
            (suzukiLogRadiusLinearCompletionToL2 v)) ≤
      (suzukiYoshidaComparisonForm v v).re +
        (suzukiLowFrequencyLogLossEnergy
          suzukiProjectAStar_pos v v).re := by
  let physical := suzukiLogRadiusLinearCompletionToL2 v
  let density : Real → Real := fun ξ =>
    ‖(FourierTransform.fourier physical : SuzukiL2) ξ‖ ^ 2
  let lowBand : Set Real :=
    Icc (-suzukiDF6D5B3FEFourierThreshold)
      suzukiDF6D5B3FEFourierThreshold
  let positiveIntegrand : Real → Real := fun ξ =>
    (suzukiLogFourierWeight ξ +
      (suzukiSourceLogNormalizationConstant - 1)) * density ξ
  have hdensity : Integrable density := by
    exact integrable_suzukiDF6D5B3FE_fourierNormSq physical
  have hweighted : Integrable (fun ξ : Real =>
      suzukiLogFourierWeight ξ * density ξ) := by
    simpa only [physical, density] using
      integrable_suzukiDF6D5B3FE_graphWeight_fourierNormSq v
  have hpositive : Integrable positiveIntegrand := by
    have hsum := hweighted.add
      (hdensity.const_mul (suzukiSourceLogNormalizationConstant - 1))
    apply hsum.congr
    filter_upwards with ξ
    dsimp only [positiveIntegrand]
    change suzukiLogFourierWeight ξ * density ξ +
        (suzukiSourceLogNormalizationConstant - 1) * density ξ =
      (suzukiLogFourierWeight ξ +
        (suzukiSourceLogNormalizationConstant - 1)) * density ξ
    ring
  have hmass :
      (∫ ξ in lowBandᶜ, density ξ) =
        ‖physical‖ ^ 2 - suzukiDF6D5B3FELowFourierMass physical := by
    rw [setIntegral_compl measurableSet_Icc hdensity]
    rw [suzukiDF6D5B3FE_integral_fourierNormSq]
    rfl
  have hpointwise : ∀ ξ ∈ lowBandᶜ,
      suzukiDF6D4DF0HighWeight * density ξ ≤ positiveIntegrand ξ := by
    intro ξ hξ
    apply mul_le_mul_of_nonneg_right
    · exact suzukiDF6D5B3FE_highWeight_le_graphWeight_add_normalization hξ
    · exact sq_nonneg _
  have hrestricted :
      (∫ ξ in lowBandᶜ,
          suzukiDF6D4DF0HighWeight * density ξ) ≤
        ∫ ξ in lowBandᶜ, positiveIntegrand ξ := by
    apply integral_mono_ae
      ((hdensity.const_mul suzukiDF6D4DF0HighWeight).integrableOn)
      hpositive.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with ξ hξ
    exact hpointwise ξ hξ
  have hdropLow :
      (∫ ξ in lowBandᶜ, positiveIntegrand ξ) ≤
        ∫ ξ : Real, positiveIntegrand ξ := by
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun ξ => mul_nonneg
        (suzukiDF6D5B3FE_graphWeight_add_normalization_nonneg ξ)
        (sq_nonneg _)) hpositive
  calc
    suzukiDF6D4DF0HighWeight *
          (‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 -
            suzukiDF6D5B3FELowFourierMass
              (suzukiLogRadiusLinearCompletionToL2 v)) =
        suzukiDF6D4DF0HighWeight *
          (∫ ξ in lowBandᶜ, density ξ) := by
      simpa only [physical] using congrArg
        (fun x : Real => suzukiDF6D4DF0HighWeight * x) hmass.symm
    _ = ∫ ξ in lowBandᶜ,
          suzukiDF6D4DF0HighWeight * density ξ := by
      rw [integral_const_mul]
    _ ≤ ∫ ξ in lowBandᶜ, positiveIntegrand ξ := hrestricted
    _ ≤ ∫ ξ : Real, positiveIntegrand ξ := hdropLow
    _ = ‖suzukiDF6D5B3FELogWeightedCoordinate v‖ ^ 2 +
          (suzukiSourceLogNormalizationConstant - 1) *
            ‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 := by
      dsimp only [positiveIntegrand]
      calc
        (∫ ξ : Real,
            (suzukiLogFourierWeight ξ +
              (suzukiSourceLogNormalizationConstant - 1)) * density ξ) =
            (∫ ξ : Real, suzukiLogFourierWeight ξ * density ξ) +
              ∫ ξ : Real,
                (suzukiSourceLogNormalizationConstant - 1) * density ξ := by
          rw [← integral_add hweighted
            (hdensity.const_mul
              (suzukiSourceLogNormalizationConstant - 1))]
          apply integral_congr_ae
          filter_upwards with ξ
          ring
        _ = ‖suzukiDF6D5B3FELogWeightedCoordinate v‖ ^ 2 +
              (suzukiSourceLogNormalizationConstant - 1) *
                ‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 := by
          rw [integral_const_mul]
          rw [show (∫ ξ : Real, suzukiLogFourierWeight ξ * density ξ) =
              ‖suzukiDF6D5B3FELogWeightedCoordinate v‖ ^ 2 by
            simpa only [physical, density] using
              (suzukiDF6D5B3FE_logWeightedCoordinate_norm_sq v).symm]
          rw [show (∫ ξ : Real, density ξ) = ‖physical‖ ^ 2 by
            simpa only [density] using
              suzukiDF6D5B3FE_integral_fourierNormSq physical]
    _ = (suzukiYoshidaComparisonForm v v).re +
          (suzukiLowFrequencyLogLossEnergy
            suzukiProjectAStar_pos v v).re :=
      (suzukiDF6D5B3FE_comparison_add_loss_self_re v).symm

/-- The completed low-frequency loss is literally a squared `L²` norm on the
diagonal. -/
theorem suzukiLowFrequencyLogLossEnergy_self_re_eq_norm_sq
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    (suzukiLowFrequencyLogLossEnergy suzukiProjectAStar_pos v v).re =
      ‖suzukiLowFrequencyWeightedFourierCompletionMap
          suzukiProjectAStar_pos v‖ ^ 2 := by
  unfold suzukiLowFrequencyLogLossEnergy
  exact inner_self_eq_norm_sq (𝕜 := Complex) _

/-- Integral realization of the completed low-frequency loss on every graph
element. -/
theorem suzukiLowFrequencyLogLossEnergy_self_re_eq_integral
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    (suzukiLowFrequencyLogLossEnergy suzukiProjectAStar_pos v v).re =
      ∫ ξ : Real, suzukiLowFrequencyLogLoss ξ *
        ‖(FourierTransform.fourier
          (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ‖ ^ 2 := by
  let weighted : SuzukiL2 :=
    suzukiLowFrequencyWeightedFourierCompletionMap suzukiProjectAStar_pos v
  have hmem : MemLp (fun ξ : Real => weighted ξ)
      (2 : ENNReal) volume := MeasureTheory.Lp.memLp weighted
  have hnorm := norm_sq_toLp_eq_integral_norm_sq
    (fun ξ : Real => weighted ξ) hmem
  rw [MeasureTheory.Lp.toLp_coeFn weighted hmem] at hnorm
  rw [suzukiLowFrequencyLogLossEnergy_self_re_eq_norm_sq]
  calc
    ‖suzukiLowFrequencyWeightedFourierCompletionMap
        suzukiProjectAStar_pos v‖ ^ 2 =
        ∫ ξ : Real, ‖weighted ξ‖ ^ 2 := by
      simpa only [weighted] using hnorm
    _ = ∫ ξ : Real, suzukiLowFrequencyLogLoss ξ *
          ‖(FourierTransform.fourier
            (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [
        suzukiLowFrequencyWeightedFourierCompletionMap_coe_ae
          suzukiProjectAStar_pos v] with ξ hξ
      dsimp only [weighted]
      rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt (suzukiLowFrequencyLogLoss_nonneg ξ)]

theorem integrable_suzukiLowFrequencyLogLoss_fourierNormSq
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    Integrable (fun ξ : Real => suzukiLowFrequencyLogLoss ξ *
      ‖(FourierTransform.fourier
        (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ‖ ^ 2) := by
  let weighted : SuzukiL2 :=
    suzukiLowFrequencyWeightedFourierCompletionMap suzukiProjectAStar_pos v
  have hnorm : Integrable (fun ξ : Real => ‖weighted ξ‖ ^ 2) :=
    (MeasureTheory.Lp.memLp weighted).integrable_norm_pow (by norm_num)
  apply hnorm.congr
  filter_upwards [
    suzukiLowFrequencyWeightedFourierCompletionMap_coe_ae
      suzukiProjectAStar_pos v] with ξ hξ
  dsimp only [weighted]
  rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (suzukiLowFrequencyLogLoss_nonneg ξ)]

theorem suzukiDF6D5B3FE_log_negativeWeightThreshold :
    Real.log suzukiDF6D5B3FENegativeWeightThreshold =
      -suzukiSourceLogNormalizationConstant := by
  have ha : suzukiProjectAStar ≠ 0 := suzukiProjectAStar_pos.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have htwoa : 2 * suzukiProjectAStar ≠ 0 := mul_ne_zero (by norm_num) ha
  have hz : suzukiDF6D4DF0ZeroCrossing ≠ 0 :=
    suzukiDF6D4DF0ZeroCrossing_pos.ne'
  have hlogtwopi : Real.log (2 * Real.pi) =
      Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) hpi
  rw [suzukiDF6D5B3FENegativeWeightThreshold, Real.log_div hz htwoa]
  unfold suzukiDF6D4DF0ZeroCrossing suzukiSourceLogNormalizationConstant
  rw [Real.log_mul (mul_ne_zero ha (Real.exp_ne_zero _)) (inv_ne_zero hpi),
    Real.log_mul ha (Real.exp_ne_zero _), Real.log_exp,
    Real.log_inv, Real.log_mul (by norm_num : (2 : Real) ≠ 0) ha]
  rw [hlogtwopi]
  ring

theorem suzukiDF6D5B3FE_normalizedNegativeWeight_eq
    {ξ : Real} (hξ : ξ ≠ 0) :
    suzukiDF6D5B3FENormalizedNegativeWeight ξ =
      -(suzukiSourceLogNormalizationConstant + Real.log |ξ|) := by
  have hc : 2 * suzukiProjectAStar ≠ 0 :=
    mul_ne_zero (by norm_num) suzukiProjectAStar_pos.ne'
  have habs : |ξ| ≠ 0 := abs_ne_zero.mpr hξ
  have hscaled : |(2 * suzukiProjectAStar) * ξ| =
      (2 * suzukiProjectAStar) * |ξ| := by
    rw [abs_mul, abs_of_pos (mul_pos (by norm_num) suzukiProjectAStar_pos)]
  unfold suzukiDF6D5B3FENormalizedNegativeWeight
  rw [hscaled]
  have hquot : suzukiDF6D4DF0ZeroCrossing /
      ((2 * suzukiProjectAStar) * |ξ|) =
        suzukiDF6D5B3FENegativeWeightThreshold / |ξ| := by
    unfold suzukiDF6D5B3FENegativeWeightThreshold
    field_simp
  rw [hquot, Real.log_div suzukiDF6D5B3FENegativeWeightThreshold_pos.ne'
    habs, suzukiDF6D5B3FE_log_negativeWeightThreshold]
  ring

theorem suzukiDF6D5B3FE_negativeWeightThreshold_lt_one :
    suzukiDF6D5B3FENegativeWeightThreshold < 1 := by
  have hz := suzukiDF6D4DF0ZeroCrossingInterval_contains.2
  have ha := fineAStarInterval_contains.1
  have hgridRat : suzukiDF6D4DF0ZeroCrossingInterval.upper <
      2 * fineAStarInterval.lower := by
    native_decide
  have hgrid : (suzukiDF6D4DF0ZeroCrossingInterval.upper : Real) <
      2 * (fineAStarInterval.lower : Real) := by
    exact_mod_cast hgridRat
  have hza : suzukiDF6D4DF0ZeroCrossing < 2 * suzukiProjectAStar := by
    calc
      suzukiDF6D4DF0ZeroCrossing ≤
          (suzukiDF6D4DF0ZeroCrossingInterval.upper : Real) := hz
      _ < 2 * (fineAStarInterval.lower : Real) := hgrid
      _ ≤ 2 * suzukiProjectAStar := by linarith
  rw [suzukiDF6D5B3FENegativeWeightThreshold,
    div_lt_one (mul_pos (by norm_num) suzukiProjectAStar_pos)]
  exact hza

/-- The pointwise source multiplier after adding back precisely its normalized
negative part. -/
def suzukiDF6D5B3FECorrectedSourceWeight (ξ : Real) : Real :=
  suzukiLogFourierWeight ξ +
      (suzukiSourceLogNormalizationConstant - 1) -
    suzukiLowFrequencyLogLoss ξ +
    (Icc (-suzukiDF6D5B3FENegativeWeightThreshold)
      suzukiDF6D5B3FENegativeWeightThreshold).indicator
        suzukiDF6D5B3FENormalizedNegativeWeight ξ

theorem suzukiDF6D5B3FECorrectedSourceWeight_nonneg (ξ : Real) :
    0 ≤ suzukiDF6D5B3FECorrectedSourceWeight ξ := by
  by_cases hband : ξ ∈ Icc (-suzukiDF6D5B3FENegativeWeightThreshold)
      suzukiDF6D5B3FENegativeWeightThreshold
  · rw [suzukiDF6D5B3FECorrectedSourceWeight, Set.indicator_of_mem hband]
    by_cases hξ : ξ = 0
    · subst ξ
      simp [suzukiLogFourierWeight, suzukiLowFrequencyLogLoss,
        suzukiDF6D5B3FENormalizedNegativeWeight,
        suzukiSourceLogNormalizationConstant_nonneg]
    · rw [suzukiDF6D5B3FE_normalizedNegativeWeight_eq hξ]
      have hbase := suzukiPosLog_sub_lowFrequencyLogLoss ξ
      unfold suzukiLogFourierWeight
      linarith
  · rw [suzukiDF6D5B3FECorrectedSourceWeight,
      Set.indicator_of_notMem hband]
    have habs : suzukiDF6D5B3FENegativeWeightThreshold ≤ |ξ| := by
      have hnot : ¬ (-suzukiDF6D5B3FENegativeWeightThreshold ≤ ξ ∧
          ξ ≤ suzukiDF6D5B3FENegativeWeightThreshold) := by
        simpa only [mem_Icc] using hband
      by_cases hleft : ξ < -suzukiDF6D5B3FENegativeWeightThreshold
      · exact le_trans (by linarith) (neg_le_abs ξ)
      · have hleft' : -suzukiDF6D5B3FENegativeWeightThreshold ≤ ξ :=
          le_of_not_gt hleft
        have hright : suzukiDF6D5B3FENegativeWeightThreshold < ξ := by
          by_contra hright
          exact hnot ⟨hleft', le_of_not_gt hright⟩
        exact hright.le.trans (le_abs_self ξ)
    have hlog := Real.log_le_log
      suzukiDF6D5B3FENegativeWeightThreshold_pos habs
    rw [suzukiDF6D5B3FE_log_negativeWeightThreshold] at hlog
    have hbase := suzukiPosLog_sub_lowFrequencyLogLoss ξ
    unfold suzukiLogFourierWeight
    linarith

theorem intervalIntegrable_suzukiDF6D5B3FE_normalizedNegativeWeight_graph
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    IntervalIntegrable (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ *
        ‖(FourierTransform.fourier
          (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ‖ ^ 2)
      volume (-suzukiDF6D5B3FENegativeWeightThreshold)
        suzukiDF6D5B3FENegativeWeightThreshold := by
  let density : Real → Real := fun ξ =>
    ‖(FourierTransform.fourier
      (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ‖ ^ 2
  have hdensity : Integrable density :=
    integrable_suzukiDF6D5B3FE_fourierNormSq
      (suzukiLogRadiusLinearCompletionToL2 v)
  have hraw : Integrable (fun ξ : Real =>
      suzukiLowFrequencyLogLoss ξ * density ξ) := by
    simpa only [density] using
      integrable_suzukiLowFrequencyLogLoss_fourierNormSq v
  have hbase : Integrable (fun ξ : Real =>
      (suzukiLowFrequencyLogLoss ξ -
        suzukiSourceLogNormalizationConstant) * density ξ) := by
    have hsub := hraw.sub
      (hdensity.const_mul suzukiSourceLogNormalizationConstant)
    apply hsub.congr
    filter_upwards with ξ
    change suzukiLowFrequencyLogLoss ξ * density ξ -
        suzukiSourceLogNormalizationConstant * density ξ = _
    ring
  apply hbase.intervalIntegrable.congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).2
  have hne : ∀ᵐ ξ : Real ∂volume, ξ ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, setOf_eq_eq_singleton] using
      (MeasureTheory.measure_singleton (μ := volume) (0 : Real))
  filter_upwards [hne] with ξ hξ
  intro hmem
  have horder : -suzukiDF6D5B3FENegativeWeightThreshold ≤
      suzukiDF6D5B3FENegativeWeightThreshold :=
    neg_le_self suzukiDF6D5B3FENegativeWeightThreshold_pos.le
  rw [uIoc_of_le horder] at hmem
  have hband : ξ ∈ Icc (-suzukiDF6D5B3FENegativeWeightThreshold)
      suzukiDF6D5B3FENegativeWeightThreshold := ⟨hmem.1.le, hmem.2⟩
  have habs : |ξ| ≤ suzukiDF6D5B3FENegativeWeightThreshold :=
    abs_le.mpr hband
  have hunit : ξ ∈ Icc (-1 : Real) 1 := by
    apply abs_le.mp
    exact habs.trans suzukiDF6D5B3FE_negativeWeightThreshold_lt_one.le
  rw [suzukiDF6D5B3FE_normalizedNegativeWeight_eq hξ,
    suzukiLowFrequencyLogLoss, Set.indicator_of_mem hunit]
  ring

theorem suzukiDF6D5B3FE_negativeWeightThreshold_lt_fourierThreshold :
    suzukiDF6D5B3FENegativeWeightThreshold <
      suzukiDF6D5B3FEFourierThreshold := by
  have hz := suzukiDF6D4DF0ZeroCrossingInterval_contains.2
  have hgridRat : suzukiDF6D4DF0ZeroCrossingInterval.upper <
      (97 / 4 : Rat) := by
    native_decide
  have hgridReal :
      (suzukiDF6D4DF0ZeroCrossingInterval.upper : Real) <
        ((97 / 4 : Rat) : Real) := by
    exact_mod_cast hgridRat
  have hzero : suzukiDF6D4DF0ZeroCrossing < (97 / 4 : Real) :=
    hz.trans_lt (by norm_num at hgridReal ⊢; exact hgridReal)
  have hden : 0 < 2 * suzukiProjectAStar :=
    mul_pos (by norm_num) suzukiProjectAStar_pos
  unfold suzukiDF6D5B3FENegativeWeightThreshold
    suzukiDF6D5B3FEFourierThreshold
  exact (div_lt_div_iff_of_pos_right hden).mpr hzero

theorem suzukiDF6D5B3FE_highWeight_le_correctedSourceWeight
    {ξ : Real}
    (hξ : ξ ∈ (Icc (-suzukiDF6D5B3FEFourierThreshold)
      suzukiDF6D5B3FEFourierThreshold)ᶜ) :
    suzukiDF6D4DF0HighWeight ≤ suzukiDF6D5B3FECorrectedSourceWeight ξ := by
  have habs : suzukiDF6D5B3FEFourierThreshold ≤ |ξ| := by
    have hnot : ¬ (-suzukiDF6D5B3FEFourierThreshold ≤ ξ ∧
        ξ ≤ suzukiDF6D5B3FEFourierThreshold) := by
      simpa only [mem_compl_iff, mem_Icc] using hξ
    by_cases hleft : ξ < -suzukiDF6D5B3FEFourierThreshold
    · exact le_trans (by linarith) (neg_le_abs ξ)
    · have hleft' : -suzukiDF6D5B3FEFourierThreshold ≤ ξ :=
        le_of_not_gt hleft
      have hright : suzukiDF6D5B3FEFourierThreshold < ξ := by
        by_contra hright
        exact hnot ⟨hleft', le_of_not_gt hright⟩
      exact hright.le.trans (le_abs_self ξ)
  have hone : 1 ≤ |ξ| := suzukiDF6D5B3FE_fourierThreshold_one_le.trans habs
  have hnotNeg : ξ ∉ Icc (-suzukiDF6D5B3FENegativeWeightThreshold)
      suzukiDF6D5B3FENegativeWeightThreshold := by
    intro hmem
    have habsUpper : |ξ| ≤ suzukiDF6D5B3FENegativeWeightThreshold :=
      abs_le.mpr hmem
    linarith [suzukiDF6D5B3FE_negativeWeightThreshold_lt_fourierThreshold]
  rw [suzukiDF6D5B3FECorrectedSourceWeight,
    Set.indicator_of_notMem hnotNeg,
    suzukiLowFrequencyLogLoss_eq_zero_of_one_le_abs hone]
  simpa only [sub_zero, add_zero] using
    suzukiDF6D5B3FE_highWeight_le_graphWeight_add_normalization hξ

theorem integrable_suzukiDF6D5B3FE_correctedSourceWeight
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    Integrable (fun ξ : Real => suzukiDF6D5B3FECorrectedSourceWeight ξ *
      ‖(FourierTransform.fourier
        (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ‖ ^ 2) := by
  let density : Real → Real := fun ξ =>
    ‖(FourierTransform.fourier
      (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ‖ ^ 2
  let band : Set Real :=
    Icc (-suzukiDF6D5B3FENegativeWeightThreshold)
      suzukiDF6D5B3FENegativeWeightThreshold
  have hdensity : Integrable density :=
    integrable_suzukiDF6D5B3FE_fourierNormSq
      (suzukiLogRadiusLinearCompletionToL2 v)
  have hgraph : Integrable (fun ξ : Real =>
      suzukiLogFourierWeight ξ * density ξ) := by
    simpa only [density] using
      integrable_suzukiDF6D5B3FE_graphWeight_fourierNormSq v
  have hraw : Integrable (fun ξ : Real =>
      suzukiLowFrequencyLogLoss ξ * density ξ) := by
    simpa only [density] using
      integrable_suzukiLowFrequencyLogLoss_fourierNormSq v
  have hnormInterval : IntervalIntegrable (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ * density ξ)
      volume (-suzukiDF6D5B3FENegativeWeightThreshold)
        suzukiDF6D5B3FENegativeWeightThreshold := by
    simpa only [density] using
      intervalIntegrable_suzukiDF6D5B3FE_normalizedNegativeWeight_graph v
  have hnormOn : IntegrableOn (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ * density ξ) band := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le
      (neg_le_self suzukiDF6D5B3FENegativeWeightThreshold_pos.le)]
    exact hnormInterval
  have hband : Integrable (band.indicator (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ * density ξ)) :=
    hnormOn.integrable_indicator measurableSet_Icc
  have hsum := ((hgraph.add
      (hdensity.const_mul (suzukiSourceLogNormalizationConstant - 1))).sub
        hraw).add hband
  apply hsum.congr
  filter_upwards with ξ
  dsimp only [density, band]
  unfold suzukiDF6D5B3FECorrectedSourceWeight
  simp only [Pi.add_apply, Pi.sub_apply]
  by_cases hmem : ξ ∈ Icc (-suzukiDF6D5B3FENegativeWeightThreshold)
      suzukiDF6D5B3FENegativeWeightThreshold
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    ring
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    ring

theorem integral_suzukiDF6D5B3FE_correctedSourceWeight
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    (∫ ξ : Real, suzukiDF6D5B3FECorrectedSourceWeight ξ *
      ‖(FourierTransform.fourier
        (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ‖ ^ 2) =
      (suzukiYoshidaComparisonForm v v).re +
        suzukiDF6D5B3FENormalizedNegativeWeightEnergy
          (suzukiLogRadiusLinearCompletionToL2 v) := by
  let physical := suzukiLogRadiusLinearCompletionToL2 v
  let density : Real → Real := fun ξ =>
    ‖(FourierTransform.fourier physical : SuzukiL2) ξ‖ ^ 2
  let band : Set Real :=
    Icc (-suzukiDF6D5B3FENegativeWeightThreshold)
      suzukiDF6D5B3FENegativeWeightThreshold
  have hdensity : Integrable density :=
    integrable_suzukiDF6D5B3FE_fourierNormSq physical
  have hgraph : Integrable (fun ξ : Real =>
      suzukiLogFourierWeight ξ * density ξ) := by
    simpa only [physical, density] using
      integrable_suzukiDF6D5B3FE_graphWeight_fourierNormSq v
  have hraw : Integrable (fun ξ : Real =>
      suzukiLowFrequencyLogLoss ξ * density ξ) := by
    simpa only [physical, density] using
      integrable_suzukiLowFrequencyLogLoss_fourierNormSq v
  have hnormOn : IntegrableOn (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ * density ξ) band := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le
      (neg_le_self suzukiDF6D5B3FENegativeWeightThreshold_pos.le)]
    simpa only [physical, density] using
      intervalIntegrable_suzukiDF6D5B3FE_normalizedNegativeWeight_graph v
  have hband : Integrable (band.indicator (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ * density ξ)) :=
    hnormOn.integrable_indicator measurableSet_Icc
  have hsplit :
      (∫ ξ : Real, suzukiDF6D5B3FECorrectedSourceWeight ξ * density ξ) =
        (∫ ξ : Real, suzukiLogFourierWeight ξ * density ξ) +
          (suzukiSourceLogNormalizationConstant - 1) *
            (∫ ξ : Real, density ξ) -
          (∫ ξ : Real, suzukiLowFrequencyLogLoss ξ * density ξ) +
          ∫ ξ : Real, band.indicator (fun ξ : Real =>
            suzukiDF6D5B3FENormalizedNegativeWeight ξ * density ξ) ξ := by
    calc
      (∫ ξ : Real, suzukiDF6D5B3FECorrectedSourceWeight ξ * density ξ) =
          ∫ ξ : Real,
            ((suzukiLogFourierWeight ξ * density ξ +
                (suzukiSourceLogNormalizationConstant - 1) * density ξ) -
              suzukiLowFrequencyLogLoss ξ * density ξ) +
              band.indicator (fun ξ : Real =>
                suzukiDF6D5B3FENormalizedNegativeWeight ξ * density ξ) ξ := by
        apply integral_congr_ae
        filter_upwards with ξ
        unfold suzukiDF6D5B3FECorrectedSourceWeight
        dsimp only [band]
        by_cases hmem : ξ ∈
            Icc (-suzukiDF6D5B3FENegativeWeightThreshold)
              suzukiDF6D5B3FENegativeWeightThreshold
        · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
          ring
        · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
          ring
      _ = (∫ ξ : Real,
            (suzukiLogFourierWeight ξ * density ξ +
                (suzukiSourceLogNormalizationConstant - 1) * density ξ) -
              suzukiLowFrequencyLogLoss ξ * density ξ) +
            ∫ ξ : Real, band.indicator (fun ξ : Real =>
              suzukiDF6D5B3FENormalizedNegativeWeight ξ * density ξ) ξ := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          integral_add
            ((hgraph.add
              (hdensity.const_mul
                (suzukiSourceLogNormalizationConstant - 1))).sub hraw)
            hband
      _ = ((∫ ξ : Real,
              suzukiLogFourierWeight ξ * density ξ +
                (suzukiSourceLogNormalizationConstant - 1) * density ξ) -
            ∫ ξ : Real, suzukiLowFrequencyLogLoss ξ * density ξ) +
            ∫ ξ : Real, band.indicator (fun ξ : Real =>
              suzukiDF6D5B3FENormalizedNegativeWeight ξ * density ξ) ξ := by
        congr 1
        simpa only [Pi.add_apply, Pi.sub_apply] using
          integral_sub
            (hgraph.add
              (hdensity.const_mul
                (suzukiSourceLogNormalizationConstant - 1))) hraw
      _ = (∫ ξ : Real, suzukiLogFourierWeight ξ * density ξ) +
            (suzukiSourceLogNormalizationConstant - 1) *
              (∫ ξ : Real, density ξ) -
            (∫ ξ : Real, suzukiLowFrequencyLogLoss ξ * density ξ) +
            ∫ ξ : Real, band.indicator (fun ξ : Real =>
              suzukiDF6D5B3FENormalizedNegativeWeight ξ * density ξ) ξ := by
        rw [show (∫ ξ : Real,
            suzukiLogFourierWeight ξ * density ξ +
              (suzukiSourceLogNormalizationConstant - 1) * density ξ) =
            (∫ ξ : Real, suzukiLogFourierWeight ξ * density ξ) +
              ∫ ξ : Real,
                (suzukiSourceLogNormalizationConstant - 1) * density ξ by
          simpa only [Pi.add_apply] using integral_add hgraph
            (hdensity.const_mul
              (suzukiSourceLogNormalizationConstant - 1))]
        rw [integral_const_mul]
  rw [show (∫ ξ : Real, suzukiDF6D5B3FECorrectedSourceWeight ξ *
      ‖(FourierTransform.fourier
        (suzukiLogRadiusLinearCompletionToL2 v) : SuzukiL2) ξ‖ ^ 2) =
      ∫ ξ : Real, suzukiDF6D5B3FECorrectedSourceWeight ξ * density ξ by rfl]
  rw [hsplit]
  rw [show (∫ ξ : Real, suzukiLogFourierWeight ξ * density ξ) =
      ‖suzukiDF6D5B3FELogWeightedCoordinate v‖ ^ 2 by
        simpa only [physical, density] using
          (suzukiDF6D5B3FE_logWeightedCoordinate_norm_sq v).symm]
  rw [show (∫ ξ : Real, density ξ) = ‖physical‖ ^ 2 by
    simpa only [density] using suzukiDF6D5B3FE_integral_fourierNormSq physical]
  rw [show (∫ ξ : Real, suzukiLowFrequencyLogLoss ξ * density ξ) =
      (suzukiLowFrequencyLogLossEnergy suzukiProjectAStar_pos v v).re by
        simpa only [physical, density] using
          (suzukiLowFrequencyLogLossEnergy_self_re_eq_integral v).symm]
  have hbandIntegral :
      (∫ ξ : Real, band.indicator (fun ξ : Real =>
        suzukiDF6D5B3FENormalizedNegativeWeight ξ * density ξ) ξ) =
        suzukiDF6D5B3FENormalizedNegativeWeightEnergy physical := by
    rw [integral_indicator measurableSet_Icc]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le
        (neg_le_self suzukiDF6D5B3FENegativeWeightThreshold_pos.le)]
    rfl
  rw [hbandIntegral]
  have hcomparison := suzukiDF6D5B3FE_comparison_add_loss_self_re v
  linarith

/-- The corrected high-band estimate adds back only the normalized negative
part of the actual source multiplier. -/
theorem suzukiDF6D5B3FE_highBandEnergyLower
    (v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    suzukiDF6D4DF0HighWeight *
        (‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 -
          suzukiDF6D5B3FELowFourierMass
            (suzukiLogRadiusLinearCompletionToL2 v)) ≤
      (suzukiYoshidaComparisonForm v v).re +
        suzukiDF6D5B3FENormalizedNegativeWeightEnergy
          (suzukiLogRadiusLinearCompletionToL2 v) := by
  let physical := suzukiLogRadiusLinearCompletionToL2 v
  let density : Real → Real := fun ξ =>
    ‖(FourierTransform.fourier physical : SuzukiL2) ξ‖ ^ 2
  let lowBand : Set Real :=
    Icc (-suzukiDF6D5B3FEFourierThreshold)
      suzukiDF6D5B3FEFourierThreshold
  let correctedIntegrand : Real → Real := fun ξ =>
    suzukiDF6D5B3FECorrectedSourceWeight ξ * density ξ
  have hdensity : Integrable density :=
    integrable_suzukiDF6D5B3FE_fourierNormSq physical
  have hcorrected : Integrable correctedIntegrand := by
    simpa only [physical, density, correctedIntegrand] using
      integrable_suzukiDF6D5B3FE_correctedSourceWeight v
  have hmass :
      (∫ ξ in lowBandᶜ, density ξ) =
        ‖physical‖ ^ 2 - suzukiDF6D5B3FELowFourierMass physical := by
    rw [setIntegral_compl measurableSet_Icc hdensity]
    rw [suzukiDF6D5B3FE_integral_fourierNormSq]
    rfl
  have hrestricted :
      (∫ ξ in lowBandᶜ,
          suzukiDF6D4DF0HighWeight * density ξ) ≤
        ∫ ξ in lowBandᶜ, correctedIntegrand ξ := by
    apply integral_mono_ae
      ((hdensity.const_mul suzukiDF6D4DF0HighWeight).integrableOn)
      hcorrected.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with ξ hξ
    exact mul_le_mul_of_nonneg_right
      (suzukiDF6D5B3FE_highWeight_le_correctedSourceWeight hξ) (sq_nonneg _)
  have hdropLow :
      (∫ ξ in lowBandᶜ, correctedIntegrand ξ) ≤
        ∫ ξ : Real, correctedIntegrand ξ := by
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun ξ =>
        mul_nonneg (suzukiDF6D5B3FECorrectedSourceWeight_nonneg ξ)
          (sq_nonneg _))
      hcorrected
  calc
    suzukiDF6D4DF0HighWeight *
          (‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 -
            suzukiDF6D5B3FELowFourierMass
              (suzukiLogRadiusLinearCompletionToL2 v)) =
        suzukiDF6D4DF0HighWeight *
          (∫ ξ in lowBandᶜ, density ξ) := by
      simpa only [physical] using congrArg
        (fun x : Real => suzukiDF6D4DF0HighWeight * x) hmass.symm
    _ = ∫ ξ in lowBandᶜ,
          suzukiDF6D4DF0HighWeight * density ξ := by
      rw [integral_const_mul]
    _ ≤ ∫ ξ in lowBandᶜ, correctedIntegrand ξ := hrestricted
    _ ≤ ∫ ξ : Real, correctedIntegrand ξ := hdropLow
    _ = (suzukiYoshidaComparisonForm v v).re +
          suzukiDF6D5B3FENormalizedNegativeWeightEnergy
            (suzukiLogRadiusLinearCompletionToL2 v) := by
      simpa only [physical, density, correctedIntegrand] using
        integral_suzukiDF6D5B3FE_correctedSourceWeight v

/-- Pure assembly of the two DF0 analytic ingredients.  `hleakage` is the
cardinal-sine low-band estimate; `hband` is the source-weight lower estimate
on the complementary Fourier band together with the certified negative
low-weight loss. -/
theorem suzukiDF6D5B3FE_localEnergyLower_mul_le_of_fourier_bounds
    {normSq lowMass energy : Real}
    (hleakage :
      lowMass ≤ suzukiDF6D4DF0LeakageFraction * normSq)
    (hband :
      suzukiDF6D4DF0HighWeight * (normSq - lowMass) -
          suzukiDF6D4DF0NegativeWeightLoss * normSq ≤ energy) :
    suzukiDF6D4DF0LocalEnergyLower * normSq ≤ energy := by
  calc
    suzukiDF6D4DF0LocalEnergyLower * normSq =
        suzukiDF6D4DF0HighWeight *
            (normSq - suzukiDF6D4DF0LeakageFraction * normSq) -
          suzukiDF6D4DF0NegativeWeightLoss * normSq := by
      unfold suzukiDF6D4DF0LocalEnergyLower
      ring
    _ ≤ suzukiDF6D4DF0HighWeight * (normSq - lowMass) -
          suzukiDF6D4DF0NegativeWeightLoss * normSq := by
      apply sub_le_sub_right
      apply mul_le_mul_of_nonneg_left _ suzukiDF6D4DF0HighWeight_nonneg
      linarith
    _ ≤ energy := hband

/-! ## Shared cardinal-sine source surfaces

The two parity calculations have the same scalar majorant.  The genuinely
analytic input is therefore stated once on the union of the two ambient
Yoshida tails.  The receiving theorems below retain the exact graph-completion
subtypes and use only the already proved containment of their physical images.
-/

/-- Literature-shaped source theorem for the DF0 low-band cardinal-sine
estimate.  Its remaining proof must start from the exact Fourier transforms of
the Yoshida modes and the cutoff-44 cardinal-sine sum; it is not an endpoint
record or a density/surjectivity assumption. -/
def SuzukiDF6D5B3FEAmbientFourierLeakage : Prop :=
  ∀ v : SuzukiL2,
    (v ∈ suzukiDF6D5B3TEvenAmbientFarSubspace ∨
      v ∈ suzukiDF6D5B3TOddAmbientFarSubspace) →
    suzukiDF6D5B3FELowFourierMass v ≤
      suzukiDF6D4DF0LeakageFraction * ‖v‖ ^ 2

/-- Shared ambient theorem for the normalized negative part of the actual
source multiplier. -/
def SuzukiDF6D5B3FEAmbientNegativeWeightLoss : Prop :=
  ∀ v : SuzukiL2,
    (v ∈ suzukiDF6D5B3TEvenAmbientFarSubspace ∨
      v ∈ suzukiDF6D5B3TOddAmbientFarSubspace) →
    suzukiDF6D5B3FENormalizedNegativeWeightEnergy v ≤
      suzukiDF6D4DF0NegativeWeightLoss * ‖v‖ ^ 2

/-- Even cardinal-sine leakage theorem on the exact parity-far domain. -/
def SuzukiDF6D5B3FEEvenFourierLeakage
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  ∀ v : certificate.EvenParityFarCompletion,
    suzukiDF6D5B3FELowFourierMass
        (suzukiLogRadiusLinearCompletionToL2 v.1) ≤
      suzukiDF6D4DF0LeakageFraction *
        ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2

/-- Odd cardinal-sine leakage theorem on the exact parity-far domain. -/
def SuzukiDF6D5B3FEOddFourierLeakage
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  ∀ v : certificate.OddParityFarCompletion,
    suzukiDF6D5B3FELowFourierMass
        (suzukiLogRadiusLinearCompletionToL2 v.1) ≤
      suzukiDF6D4DF0LeakageFraction *
        ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2

/-- Even high-band source-weight estimate before subtracting the completed
low-frequency logarithmic loss.  Unlike the leakage estimates, this theorem
does not use parity or vanishing low Yoshida coordinates; those facts remain
visible in the receiving type only so its consumer is exact. -/
def SuzukiDF6D5B3FEEvenHighBandEnergyLower
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  ∀ v : certificate.EvenParityFarCompletion,
    suzukiDF6D4DF0HighWeight *
        (‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 -
          suzukiDF6D5B3FELowFourierMass
            (suzukiLogRadiusLinearCompletionToL2 v.1)) ≤
      (suzukiYoshidaComparisonForm v.1 v.1).re +
        suzukiDF6D5B3FENormalizedNegativeWeightEnergy
          (suzukiLogRadiusLinearCompletionToL2 v.1)

/-- Odd high-band source-weight estimate before subtracting the completed
low-frequency logarithmic loss. -/
def SuzukiDF6D5B3FEOddHighBandEnergyLower
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  ∀ v : certificate.OddParityFarCompletion,
    suzukiDF6D4DF0HighWeight *
        (‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 -
          suzukiDF6D5B3FELowFourierMass
            (suzukiLogRadiusLinearCompletionToL2 v.1)) ≤
      (suzukiYoshidaComparisonForm v.1 v.1).re +
        suzukiDF6D5B3FENormalizedNegativeWeightEnergy
          (suzukiLogRadiusLinearCompletionToL2 v.1)

/-- Even cardinal-sine bound for the negative part of the logarithmic
source multiplier. -/
def SuzukiDF6D5B3FEEvenNegativeWeightLoss
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  ∀ v : certificate.EvenParityFarCompletion,
    suzukiDF6D5B3FENormalizedNegativeWeightEnergy
        (suzukiLogRadiusLinearCompletionToL2 v.1) ≤
      suzukiDF6D4DF0NegativeWeightLoss *
        ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2

/-- Odd cardinal-sine bound for the negative part of the logarithmic source
multiplier. -/
def SuzukiDF6D5B3FEOddNegativeWeightLoss
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  ∀ v : certificate.OddParityFarCompletion,
    suzukiDF6D5B3FENormalizedNegativeWeightEnergy
        (suzukiLogRadiusLinearCompletionToL2 v.1) ≤
      suzukiDF6D4DF0NegativeWeightLoss *
        ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2

/-- The shared ambient leakage theorem specializes to the exact even graph
receiver for the canonical B2S source certificate. -/
theorem suzukiDF6D5B3FE_evenFourierLeakage_of_ambient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hleakage : SuzukiDF6D5B3FEAmbientFourierLeakage) :
    SuzukiDF6D5B3FEEvenFourierLeakage
      (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  intro v
  apply hleakage _ (Or.inl ?_)
  apply
    suzukiProjectB3T_evenParityFarL2Subspace_le_ambient_of_source
      hsource
  exact ⟨v.1, v.2, rfl⟩

/-- The shared ambient leakage theorem specializes to the exact odd graph
receiver for the canonical B2S source certificate. -/
theorem suzukiDF6D5B3FE_oddFourierLeakage_of_ambient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hleakage : SuzukiDF6D5B3FEAmbientFourierLeakage) :
    SuzukiDF6D5B3FEOddFourierLeakage
      (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  intro v
  apply hleakage _ (Or.inr ?_)
  apply
    suzukiProjectB3T_oddParityFarL2Subspace_le_ambient_of_source
      hsource
  exact ⟨v.1, v.2, rfl⟩

/-- The shared ambient negative-loss theorem specializes to the exact even
graph receiver for the canonical B2S source certificate. -/
theorem suzukiDF6D5B3FE_evenNegativeWeightLoss_of_ambient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hloss : SuzukiDF6D5B3FEAmbientNegativeWeightLoss) :
    SuzukiDF6D5B3FEEvenNegativeWeightLoss
      (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  intro v
  apply hloss (suzukiLogRadiusLinearCompletionToL2 v.1) (Or.inl ?_)
  apply
    suzukiProjectB3T_evenParityFarL2Subspace_le_ambient_of_source
      hsource
  exact ⟨v.1, v.2, rfl⟩

/-- The shared ambient negative-loss theorem specializes to the exact odd
graph receiver for the canonical B2S source certificate. -/
theorem suzukiDF6D5B3FE_oddNegativeWeightLoss_of_ambient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hloss : SuzukiDF6D5B3FEAmbientNegativeWeightLoss) :
    SuzukiDF6D5B3FEOddNegativeWeightLoss
      (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  intro v
  apply hloss (suzukiLogRadiusLinearCompletionToL2 v.1) (Or.inr ?_)
  apply
    suzukiProjectB3T_oddParityFarL2Subspace_le_ambient_of_source
      hsource
  exact ⟨v.1, v.2, rfl⟩

/-- The universal completed-domain theorem fills the even high-band target. -/
theorem suzukiDF6D5B3FE_evenHighBandEnergyLower
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) :
    SuzukiDF6D5B3FEEvenHighBandEnergyLower certificate := by
  intro v
  exact suzukiDF6D5B3FE_highBandEnergyLower v.1

/-- The universal completed-domain theorem fills the odd high-band target. -/
theorem suzukiDF6D5B3FE_oddHighBandEnergyLower
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) :
    SuzukiDF6D5B3FEOddHighBandEnergyLower certificate := by
  intro v
  exact suzukiDF6D5B3FE_highBandEnergyLower v.1

/-- Even source-weight estimate after splitting at the DF0 Fourier cutoff.
The remaining negative low-weight contribution is bounded by the explicit
DF0 loss constant. -/
def SuzukiDF6D5B3FEEvenFourierBandEnergyLower
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  ∀ v : certificate.EvenParityFarCompletion,
    suzukiDF6D4DF0HighWeight *
        (‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 -
          suzukiDF6D5B3FELowFourierMass
            (suzukiLogRadiusLinearCompletionToL2 v.1)) -
        suzukiDF6D4DF0NegativeWeightLoss *
          ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 ≤
      (suzukiYoshidaComparisonForm v.1 v.1).re

/-- Odd source-weight estimate after splitting at the DF0 Fourier cutoff. -/
def SuzukiDF6D5B3FEOddFourierBandEnergyLower
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  ∀ v : certificate.OddParityFarCompletion,
    suzukiDF6D4DF0HighWeight *
        (‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 -
          suzukiDF6D5B3FELowFourierMass
            (suzukiLogRadiusLinearCompletionToL2 v.1)) -
        suzukiDF6D4DF0NegativeWeightLoss *
          ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 ≤
      (suzukiYoshidaComparisonForm v.1 v.1).re

/-- The even high-band multiplier estimate and negative-weight estimate give
the combined Fourier-band input used by the scalar assembly lemma. -/
theorem suzukiDF6D5B3FE_evenFourierBandEnergyLower_of_components
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (hhigh : SuzukiDF6D5B3FEEvenHighBandEnergyLower certificate)
    (hloss : SuzukiDF6D5B3FEEvenNegativeWeightLoss certificate) :
    SuzukiDF6D5B3FEEvenFourierBandEnergyLower certificate := by
  intro v
  have hhighv := hhigh v
  have hlossv := hloss v
  linarith

/-- The odd high-band multiplier estimate and negative-weight estimate give
the combined Fourier-band input used by the scalar assembly lemma. -/
theorem suzukiDF6D5B3FE_oddFourierBandEnergyLower_of_components
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (hhigh : SuzukiDF6D5B3FEOddHighBandEnergyLower certificate)
    (hloss : SuzukiDF6D5B3FEOddNegativeWeightLoss certificate) :
    SuzukiDF6D5B3FEOddFourierBandEnergyLower certificate := by
  intro v
  have hhighv := hhigh v
  have hlossv := hloss v
  linarith

/-- Sharp even B3F-E source theorem on the exact matching parity-far domain.
This is the functional inequality whose DF0 scalar was already independently
certified. -/
def SuzukiDF6D5B3FEEvenSharpEnergyLower
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  ∀ v : certificate.EvenParityFarCompletion,
    suzukiDF6D4DF0LocalEnergyLower *
        ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 ≤
      (suzukiYoshidaComparisonForm v.1 v.1).re

/-- Sharp odd B3F-E source theorem on the exact matching parity-far domain. -/
def SuzukiDF6D5B3FEOddSharpEnergyLower
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  ∀ v : certificate.OddParityFarCompletion,
    suzukiDF6D4DF0LocalEnergyLower *
        ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 ≤
      (suzukiYoshidaComparisonForm v.1 v.1).re

/-- The two concrete even Fourier estimates assemble to the sharp B3F-E
source theorem. -/
theorem suzukiDF6D5B3FE_evenSharpEnergyLower_of_fourier_bounds
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (hleakage : SuzukiDF6D5B3FEEvenFourierLeakage certificate)
    (hband : SuzukiDF6D5B3FEEvenFourierBandEnergyLower certificate) :
    SuzukiDF6D5B3FEEvenSharpEnergyLower certificate := by
  intro v
  exact suzukiDF6D5B3FE_localEnergyLower_mul_le_of_fourier_bounds
    (hleakage v) (hband v)

/-- The two concrete odd Fourier estimates assemble to the sharp B3F-E
source theorem. -/
theorem suzukiDF6D5B3FE_oddSharpEnergyLower_of_fourier_bounds
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (hleakage : SuzukiDF6D5B3FEOddFourierLeakage certificate)
    (hband : SuzukiDF6D5B3FEOddFourierBandEnergyLower certificate) :
    SuzukiDF6D5B3FEOddSharpEnergyLower certificate := by
  intro v
  exact suzukiDF6D5B3FE_localEnergyLower_mul_le_of_fourier_bounds
    (hleakage v) (hband v)

/-- The two genuinely high-mode even cardinal-sine estimates imply the sharp
B3F-E theorem; the high-band multiplier theorem is discharged internally. -/
theorem suzukiDF6D5B3FE_evenSharpEnergyLower_of_cardinalSine
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (hleakage : SuzukiDF6D5B3FEEvenFourierLeakage certificate)
    (hloss : SuzukiDF6D5B3FEEvenNegativeWeightLoss certificate) :
    SuzukiDF6D5B3FEEvenSharpEnergyLower certificate := by
  apply suzukiDF6D5B3FE_evenSharpEnergyLower_of_fourier_bounds hleakage
  exact suzukiDF6D5B3FE_evenFourierBandEnergyLower_of_components
    (suzukiDF6D5B3FE_evenHighBandEnergyLower certificate) hloss

/-- The two genuinely high-mode odd cardinal-sine estimates imply the sharp
B3F-E theorem; the high-band multiplier theorem is discharged internally. -/
theorem suzukiDF6D5B3FE_oddSharpEnergyLower_of_cardinalSine
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (hleakage : SuzukiDF6D5B3FEOddFourierLeakage certificate)
    (hloss : SuzukiDF6D5B3FEOddNegativeWeightLoss certificate) :
    SuzukiDF6D5B3FEOddSharpEnergyLower certificate := by
  apply suzukiDF6D5B3FE_oddSharpEnergyLower_of_fourier_bounds hleakage
  exact suzukiDF6D5B3FE_oddFourierBandEnergyLower_of_components
    (suzukiDF6D5B3FE_oddHighBandEnergyLower certificate) hloss

/-- Canonical B3F-E reduction: the two shared ambient cardinal-sine source
theorems give both sharp parity bounds on the exact B2S graph receivers. -/
theorem suzukiDF6D5B3FE_canonicalSharpEnergyLower_of_ambientCardinalSine
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hleakage : SuzukiDF6D5B3FEAmbientFourierLeakage)
    (hloss : SuzukiDF6D5B3FEAmbientNegativeWeightLoss) :
    SuzukiDF6D5B3FEEvenSharpEnergyLower
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) ∧
      SuzukiDF6D5B3FEOddSharpEnergyLower
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  constructor
  · exact suzukiDF6D5B3FE_evenSharpEnergyLower_of_cardinalSine
      (suzukiDF6D5B3FE_evenFourierLeakage_of_ambient
        hsource hleakage)
      (suzukiDF6D5B3FE_evenNegativeWeightLoss_of_ambient
        hsource hloss)
  · exact suzukiDF6D5B3FE_oddSharpEnergyLower_of_cardinalSine
      (suzukiDF6D5B3FE_oddFourierLeakage_of_ambient
        hsource hleakage)
      (suzukiDF6D5B3FE_oddNegativeWeightLoss_of_ambient
        hsource hloss)

/-- The sharp even source theorem implies the uniform `E ≥ 5 I` estimate. -/
theorem suzukiDF6D5B3FE_even_five_mul_norm_sq_le
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (hsharp : SuzukiDF6D5B3FEEvenSharpEnergyLower certificate)
    (v : certificate.EvenParityFarCompletion) :
    5 * ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 ≤
      (suzukiYoshidaComparisonForm v.1 v.1).re := by
  exact
    (mul_le_mul_of_nonneg_right
      suzukiDF6D4DF0LocalEnergyLower_gt_five.le
      (sq_nonneg ‖suzukiLogRadiusLinearCompletionToL2 v.1‖)).trans
        (hsharp v)

/-- The sharp odd source theorem implies the uniform `E ≥ 5 I` estimate. -/
theorem suzukiDF6D5B3FE_odd_five_mul_norm_sq_le
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (hsharp : SuzukiDF6D5B3FEOddSharpEnergyLower certificate)
    (v : certificate.OddParityFarCompletion) :
    5 * ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 ≤
      (suzukiYoshidaComparisonForm v.1 v.1).re := by
  exact
    (mul_le_mul_of_nonneg_right
      suzukiDF6D4DF0LocalEnergyLower_gt_five.le
      (sq_nonneg ‖suzukiLogRadiusLinearCompletionToL2 v.1‖)).trans
        (hsharp v)

/-- Reciprocal `1/5` estimate used by the even B3R-E residual bound. -/
theorem suzukiDF6D5B3FE_even_norm_sq_le_one_fifth_energy
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (hsharp : SuzukiDF6D5B3FEEvenSharpEnergyLower certificate)
    (v : certificate.EvenParityFarCompletion) :
    ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 ≤
      (1 / 5 : Real) * (suzukiYoshidaComparisonForm v.1 v.1).re := by
  have hfive := suzukiDF6D5B3FE_even_five_mul_norm_sq_le hsharp v
  linarith

/-- Reciprocal `1/5` estimate used by the odd B3R-E residual bound. -/
theorem suzukiDF6D5B3FE_odd_norm_sq_le_one_fifth_energy
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (hsharp : SuzukiDF6D5B3FEOddSharpEnergyLower certificate)
    (v : certificate.OddParityFarCompletion) :
    ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 ≤
      (1 / 5 : Real) * (suzukiYoshidaComparisonForm v.1 v.1).re := by
  have hfive := suzukiDF6D5B3FE_odd_five_mul_norm_sq_le hsharp v
  linarith

/-- The sharp even comparison-energy theorem fills B3T's corrected physical
far-coercivity receiver for `E`. -/
theorem suzukiDF6D5B3T_evenFarCoercivity_comparison_of_sharp
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (hsharp : SuzukiDF6D5B3FEEvenSharpEnergyLower certificate) :
    SuzukiDF6D5B3TEvenFarCoercivity certificate
      suzukiYoshidaComparisonHermitianForm := by
  intro v
  have hfive := suzukiDF6D5B3FE_even_five_mul_norm_sq_le hsharp v
  change
    2 * ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 ≤
      (suzukiYoshidaComparisonForm v.1 v.1).re
  nlinarith [sq_nonneg ‖suzukiLogRadiusLinearCompletionToL2 v.1‖]

/-- The sharp odd comparison-energy theorem fills B3T's corrected physical
far-coercivity receiver for `E`. -/
theorem suzukiDF6D5B3T_oddFarCoercivity_comparison_of_sharp
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (hsharp : SuzukiDF6D5B3FEOddSharpEnergyLower certificate) :
    SuzukiDF6D5B3TOddFarCoercivity certificate
      suzukiYoshidaComparisonHermitianForm := by
  intro v
  have hfive := suzukiDF6D5B3FE_odd_five_mul_norm_sq_le hsharp v
  change
    2 * ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 ≤
      (suzukiYoshidaComparisonForm v.1 v.1).re
  nlinarith [sq_nonneg ‖suzukiLogRadiusLinearCompletionToL2 v.1‖]

end

end RiemannHypothesisProject.Experiments.M100
