import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaGammaPrimitiveVariation
import RiemannHypothesisProject.Experiments.M100.SuzukiL2SupportTranslationBound

/-!
# Corrected complete-energy coercivity for M100-DF6D5B3F-F

This module freezes the exact B3F-F receiving surfaces.  The already checked
B3F-E comparison-energy theorem is combined with the signed DF0 identity.
The prime-`2` estimate is stated on the whole common form domain; the only
high-mode analytic input is the Gamma-remainder estimate on the union of the
two ambient parity tails.

No positivity premise is bundled into an endpoint certificate.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

/-- B3V's corrected complete form bundled for the B3T receiving surfaces. -/
def suzukiYoshidaCorrectedCompleteHermitianForm :
    SuzukiDF6D5B3THermitianForm where
  toFun := suzukiYoshidaCorrectedCompleteForm
  conj_symm := suzukiYoshidaCorrectedCompleteForm_conj_symm

/-- Elementary prime-`2` estimate on the whole completed form domain.  Its
proof is support geometry: split at the origin and use
`log 2 > suzukiProjectAStar` to make the two translated pieces disjoint. -/
def SuzukiDF6D5B3FFPrimeBound : Prop :=
  ∀ v : SuzukiYoshidaCorrectedCommonFormDomain,
    abs (suzukiYoshidaPrimeTwoForm v v).re ≤
      suzukiDF6D4DF0PrimeNorm *
        ‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2

theorem suzukiProjectAStar_lt_log_two :
    suzukiProjectAStar < Real.log 2 := by
  have hA := fineAStarInterval_contains
  have hL := fineLogTwoInterval_contains
  unfold fineAStarInterval RationalInterval.Contains at hA
  unfold fineLogTwoInterval RationalInterval.Contains at hL
  norm_num at hA hL ⊢
  linarith

/-- The support-sharp translation estimate proves the complete prime-`2`
bound; it is not an analytic premise of B3F-F. -/
theorem suzukiDF6D5B3FFPrimeBound_of_support :
    SuzukiDF6D5B3FFPrimeBound := by
  intro v
  have hdiagonal :=
    suzukiL2SymmetricTranslationDiagonal_abs_le_of_supportedAt
      suzukiProjectAStar_lt_log_two
      (suzukiLogRadiusLinearCompletionToL2_supportedAt v)
  rw [suzukiYoshidaPrimeTwoForm,
    suzukiL2FiniteTranslationEnergy_self_re,
    suzukiProjectPrimeIndexSet_at_aStar]
  unfold suzukiL2FiniteTranslationRemainder
  simp only [Finset.sum_singleton]
  have hcoefficient :
      suzukiProjectPrimeCoefficient 2 =
        -(Real.log 2 / Real.sqrt 2) := by
    unfold suzukiProjectPrimeCoefficient
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  rw [hcoefficient]
  unfold suzukiProjectPrimeShift suzukiDF6D4DF0PrimeNorm
  rw [abs_mul, abs_neg, abs_of_nonneg
    (div_nonneg (Real.log_pos (by norm_num)).le (Real.sqrt_nonneg 2))]
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hdiagonal
    (mul_nonneg (Real.log_pos (by norm_num)).le
      (inv_nonneg.mpr (Real.sqrt_nonneg 2)))

/-- The single literature-shaped analytic input left by B3F-F: the
cutoff-44 primitive/variation estimate for the smooth Gamma remainder on the
union of the two ambient Yoshida tails. -/
def SuzukiDF6D5B3FFAmbientGammaRemainderBound : Prop :=
  ∀ v : SuzukiL2,
    (v ∈ suzukiDF6D5B3TEvenAmbientFarSubspace ∨
      v ∈ suzukiDF6D5B3TOddAmbientFarSubspace) →
    abs (suzukiL2BoundedOperatorEnergy
        (suzukiRSecondGlobalL2Operator suzukiProjectAStar) v v).re ≤
      suzukiDF6D4DF0RemainderNorm * ‖v‖ ^ 2

/-- The remaining analytic statement after the cutoff-44 primitive operator
has been constructed and bounded: integration by parts must control the
`r''` pairing by total variation times the canonical primitive norm. -/
def SuzukiDF6D5B3FFAmbientGammaPrimitiveVariationBound : Prop :=
  ∀ (v : SuzukiL2)
    (hv : v ∈ suzukiDF6D5B3TEvenAmbientFarSubspace ∨
      v ∈ suzukiDF6D5B3TOddAmbientFarSubspace),
    abs (suzukiL2BoundedOperatorEnergy
        (suzukiRSecondGlobalL2Operator suzukiProjectAStar) v v).re ≤
      suzukiDF6D4DF0RemainderVariation *
        ‖cutoff44HighAmbientPrimitive v hv‖ * ‖v‖

/-- The closed cutoff-44 primitive-variation theorem discharges the ambient
Gamma premise on the union of the two exact parity tails. -/
theorem suzukiDF6D5B3FFAmbientGammaPrimitiveVariationBound_proved :
    SuzukiDF6D5B3FFAmbientGammaPrimitiveVariationBound := by
  intro v hv
  have hvClosure :
      v ∈ cutoff44HighExponentialSubspace.topologicalClosure := by
    rcases hv with heven | hodd
    · exact suzukiDF6D5B3TEvenAmbientFarSubspace_le_cutoff44HighClosure heven
    · exact suzukiDF6D5B3TOddAmbientFarSubspace_le_cutoff44HighClosure hodd
  let w : cutoff44HighExponentialSubspace.topologicalClosure :=
    ⟨v, hvClosure⟩
  have hclosure :=
    abs_re_suzukiRSecondGlobalL2OperatorEnergy_cutoff44HighClosure_le w
  unfold cutoff44HighAmbientPrimitive
  simpa only [w, Submodule.coe_norm] using hclosure

theorem suzukiDF6D5B3FF_remainderVariation_nonneg :
    0 ≤ suzukiDF6D4DF0RemainderVariation := by
  have hcontains := suzukiDF6D4DF0RemainderVariationInterval_contains
  have hlower : (0 : Rat) ≤
      suzukiDF6D4DF0RemainderVariationInterval.lower := by native_decide
  have hzero : (0 : Real) ≤
      (suzukiDF6D4DF0RemainderVariationInterval.lower : Rat) := by
    exact_mod_cast hlower
  exact hzero.trans hcontains.1

/-- The primitive/variation theorem discharges the sole B3F-F Gamma
receiver; the sharp primitive norm is no longer an assumption. -/
theorem suzukiDF6D5B3FFAmbientGammaRemainderBound_of_primitiveVariation
    (hvariation : SuzukiDF6D5B3FFAmbientGammaPrimitiveVariationBound) :
    SuzukiDF6D5B3FFAmbientGammaRemainderBound := by
  intro v hv
  have hprimitive := norm_cutoff44HighAmbientPrimitive_le_DF0 v hv
  calc
    abs (suzukiL2BoundedOperatorEnergy
        (suzukiRSecondGlobalL2Operator suzukiProjectAStar) v v).re ≤
      suzukiDF6D4DF0RemainderVariation *
        ‖cutoff44HighAmbientPrimitive v hv‖ * ‖v‖ := hvariation v hv
    _ ≤ suzukiDF6D4DF0RemainderVariation *
        (suzukiDF6D4DF0PrimitiveNorm * ‖v‖) * ‖v‖ := by
      gcongr
      exact suzukiDF6D5B3FF_remainderVariation_nonneg
    _ = suzukiDF6D4DF0RemainderNorm * ‖v‖ ^ 2 := by
      unfold suzukiDF6D4DF0RemainderNorm
      ring

/-- Unconditional ambient Gamma remainder bound at the frozen DF0 constant. -/
theorem suzukiDF6D5B3FFAmbientGammaRemainderBound_proved :
    SuzukiDF6D5B3FFAmbientGammaRemainderBound :=
  suzukiDF6D5B3FFAmbientGammaRemainderBound_of_primitiveVariation
    suzukiDF6D5B3FFAmbientGammaPrimitiveVariationBound_proved

/-- The ambient Gamma theorem specializes to the exact canonical even graph
receiver. -/
theorem suzukiDF6D5B3FF_evenGammaRemainderBound_of_ambient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hgamma : SuzukiDF6D5B3FFAmbientGammaRemainderBound)
    (v : (suzukiProjectB2EndpointModeCertificateOfSource hsource).EvenParityFarCompletion) :
    abs (suzukiYoshidaGammaRemainderForm v.1 v.1).re ≤
      suzukiDF6D4DF0RemainderNorm *
        ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 := by
  unfold suzukiYoshidaGammaRemainderForm
  apply hgamma _ (Or.inl ?_)
  apply
    suzukiProjectB3T_evenParityFarL2Subspace_le_ambient_of_source
      hsource
  exact ⟨v.1, v.2, rfl⟩

/-- The ambient Gamma theorem specializes to the exact canonical odd graph
receiver. -/
theorem suzukiDF6D5B3FF_oddGammaRemainderBound_of_ambient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hgamma : SuzukiDF6D5B3FFAmbientGammaRemainderBound)
    (v : (suzukiProjectB2EndpointModeCertificateOfSource hsource).OddParityFarCompletion) :
    abs (suzukiYoshidaGammaRemainderForm v.1 v.1).re ≤
      suzukiDF6D4DF0RemainderNorm *
        ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2 := by
  unfold suzukiYoshidaGammaRemainderForm
  apply hgamma _ (Or.inr ?_)
  apply
    suzukiProjectB3T_oddParityFarL2Subspace_le_ambient_of_source
      hsource
  exact ⟨v.1, v.2, rfl⟩

/-- Pure even B3F-F assembly from the sharp comparison energy and the two
visible bounded corrections. -/
theorem suzukiDF6D5B3FF_even_complete_ge_two_fifths
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (henergy : SuzukiDF6D5B3FEEvenSharpEnergyLower certificate)
    (hprime : SuzukiDF6D5B3FFPrimeBound)
    (hgamma : ∀ v : certificate.EvenParityFarCompletion,
      abs (suzukiYoshidaGammaRemainderForm v.1 v.1).re ≤
        suzukiDF6D4DF0RemainderNorm *
          ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2)
    (v : certificate.EvenParityFarCompletion) :
    (2 / 5 : Real) * (suzukiYoshidaComparisonForm v.1 v.1).re ≤
      (suzukiYoshidaCorrectedCompleteForm v.1 v.1).re := by
  have h := suzukiDF6D4DF0_form_ge_two_fifths
    (qF := (suzukiYoshidaCorrectedCompleteForm v.1 v.1).re)
    (qE := (suzukiYoshidaComparisonForm v.1 v.1).re)
    (normSq := ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2)
    (prime := (suzukiYoshidaPrimeTwoForm v.1 v.1).re)
    (remainder := (suzukiYoshidaGammaRemainderForm v.1 v.1).re)
    (sq_nonneg _)
    (suzukiYoshidaCorrectedCompleteForm_self_re_eq_df0_signed v.1)
    (henergy v) (hprime v.1) (hgamma v)
  have hmargin : 0 ≤ suzukiDF6D4DF0TwoFifthsMargin :=
    (lt_trans (by norm_num : (0 : Real) < 1 / 10)
      suzukiDF6D4DF0TwoFifthsMargin_gt_one_tenth).le
  nlinarith [sq_nonneg ‖suzukiLogRadiusLinearCompletionToL2 v.1‖]

/-- Pure odd B3F-F assembly. -/
theorem suzukiDF6D5B3FF_odd_complete_ge_two_fifths
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (henergy : SuzukiDF6D5B3FEOddSharpEnergyLower certificate)
    (hprime : SuzukiDF6D5B3FFPrimeBound)
    (hgamma : ∀ v : certificate.OddParityFarCompletion,
      abs (suzukiYoshidaGammaRemainderForm v.1 v.1).re ≤
        suzukiDF6D4DF0RemainderNorm *
          ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2)
    (v : certificate.OddParityFarCompletion) :
    (2 / 5 : Real) * (suzukiYoshidaComparisonForm v.1 v.1).re ≤
      (suzukiYoshidaCorrectedCompleteForm v.1 v.1).re := by
  have h := suzukiDF6D4DF0_form_ge_two_fifths
    (qF := (suzukiYoshidaCorrectedCompleteForm v.1 v.1).re)
    (qE := (suzukiYoshidaComparisonForm v.1 v.1).re)
    (normSq := ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2)
    (prime := (suzukiYoshidaPrimeTwoForm v.1 v.1).re)
    (remainder := (suzukiYoshidaGammaRemainderForm v.1 v.1).re)
    (sq_nonneg _)
    (suzukiYoshidaCorrectedCompleteForm_self_re_eq_df0_signed v.1)
    (henergy v) (hprime v.1) (hgamma v)
  have hmargin : 0 ≤ suzukiDF6D4DF0TwoFifthsMargin :=
    (lt_trans (by norm_num : (0 : Real) < 1 / 10)
      suzukiDF6D4DF0TwoFifthsMargin_gt_one_tenth).le
  nlinarith [sq_nonneg ‖suzukiLogRadiusLinearCompletionToL2 v.1‖]

/-- Even comparison energy is at most `5/2` times the corrected complete
energy, in the exact shape consumed by B3R. -/
theorem suzukiDF6D5B3FF_even_comparison_le_five_halves_complete
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (henergy : SuzukiDF6D5B3FEEvenSharpEnergyLower certificate)
    (hprime : SuzukiDF6D5B3FFPrimeBound)
    (hgamma : ∀ v : certificate.EvenParityFarCompletion,
      abs (suzukiYoshidaGammaRemainderForm v.1 v.1).re ≤
        suzukiDF6D4DF0RemainderNorm *
          ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2)
    (v : certificate.EvenParityFarCompletion) :
    (suzukiYoshidaComparisonForm v.1 v.1).re ≤
      (5 / 2 : Real) *
        (suzukiYoshidaCorrectedCompleteForm v.1 v.1).re := by
  have h := suzukiDF6D5B3FF_even_complete_ge_two_fifths
    henergy hprime hgamma v
  nlinarith

/-- Odd comparison-to-complete order used by B3R. -/
theorem suzukiDF6D5B3FF_odd_comparison_le_five_halves_complete
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (henergy : SuzukiDF6D5B3FEOddSharpEnergyLower certificate)
    (hprime : SuzukiDF6D5B3FFPrimeBound)
    (hgamma : ∀ v : certificate.OddParityFarCompletion,
      abs (suzukiYoshidaGammaRemainderForm v.1 v.1).re ≤
        suzukiDF6D4DF0RemainderNorm *
          ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2)
    (v : certificate.OddParityFarCompletion) :
    (suzukiYoshidaComparisonForm v.1 v.1).re ≤
      (5 / 2 : Real) *
        (suzukiYoshidaCorrectedCompleteForm v.1 v.1).re := by
  have h := suzukiDF6D5B3FF_odd_complete_ge_two_fifths
    henergy hprime hgamma v
  nlinarith

/-- The even two-fifths comparison implies corrected complete-form
coercivity with coefficient `2`. -/
theorem suzukiDF6D5B3FF_evenFarCoercivity_of_bounds
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (henergy : SuzukiDF6D5B3FEEvenSharpEnergyLower certificate)
    (hprime : SuzukiDF6D5B3FFPrimeBound)
    (hgamma : ∀ v : certificate.EvenParityFarCompletion,
      abs (suzukiYoshidaGammaRemainderForm v.1 v.1).re ≤
        suzukiDF6D4DF0RemainderNorm *
          ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2) :
    SuzukiDF6D5B3TEvenFarCoercivity certificate
      suzukiYoshidaCorrectedCompleteHermitianForm := by
  intro v
  exact (suzukiDF6D4DF0_two_fifths_energy_ge_two
    (sq_nonneg _) (henergy v)).trans
      (suzukiDF6D5B3FF_even_complete_ge_two_fifths
        henergy hprime hgamma v)

/-- Odd corrected complete-form coercivity with coefficient `2`. -/
theorem suzukiDF6D5B3FF_oddFarCoercivity_of_bounds
    {certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar}
    (henergy : SuzukiDF6D5B3FEOddSharpEnergyLower certificate)
    (hprime : SuzukiDF6D5B3FFPrimeBound)
    (hgamma : ∀ v : certificate.OddParityFarCompletion,
      abs (suzukiYoshidaGammaRemainderForm v.1 v.1).re ≤
        suzukiDF6D4DF0RemainderNorm *
          ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ ^ 2) :
    SuzukiDF6D5B3TOddFarCoercivity certificate
      suzukiYoshidaCorrectedCompleteHermitianForm := by
  intro v
  exact (suzukiDF6D4DF0_two_fifths_energy_ge_two
    (sq_nonneg _) (henergy v)).trans
      (suzukiDF6D5B3FF_odd_complete_ge_two_fifths
        henergy hprime hgamma v)

/-- Canonical B3F-F endpoint: after the universal prime geometry and the
single ambient Gamma estimate, both exact parity-far receivers are filled. -/
theorem suzukiDF6D5B3FF_canonicalFarCoercivity_of_source
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hgamma : SuzukiDF6D5B3FFAmbientGammaRemainderBound) :
    SuzukiDF6D5B3TEvenFarCoercivity
        (suzukiProjectB2EndpointModeCertificateOfSource hsource)
        suzukiYoshidaCorrectedCompleteHermitianForm ∧
      SuzukiDF6D5B3TOddFarCoercivity
        (suzukiProjectB2EndpointModeCertificateOfSource hsource)
        suzukiYoshidaCorrectedCompleteHermitianForm := by
  have henergy := suzukiDF6D5B3FE_canonicalSharpEnergyLower_of_source hsource
  exact ⟨
    suzukiDF6D5B3FF_evenFarCoercivity_of_bounds henergy.1
      suzukiDF6D5B3FFPrimeBound_of_support
      (suzukiDF6D5B3FF_evenGammaRemainderBound_of_ambient hsource hgamma),
    suzukiDF6D5B3FF_oddFarCoercivity_of_bounds henergy.2
      suzukiDF6D5B3FFPrimeBound_of_support
      (suzukiDF6D5B3FF_oddGammaRemainderBound_of_ambient hsource hgamma)⟩

/-- Unconditional B3F-F endpoint relative only to the visible B2S source
premise: both corrected complete-form parity-far coercivity statements hold. -/
theorem suzukiDF6D5B3FF_canonicalFarCoercivity
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiDF6D5B3TEvenFarCoercivity
        (suzukiProjectB2EndpointModeCertificateOfSource hsource)
        suzukiYoshidaCorrectedCompleteHermitianForm ∧
      SuzukiDF6D5B3TOddFarCoercivity
        (suzukiProjectB2EndpointModeCertificateOfSource hsource)
        suzukiYoshidaCorrectedCompleteHermitianForm :=
  suzukiDF6D5B3FF_canonicalFarCoercivity_of_source hsource
    suzukiDF6D5B3FFAmbientGammaRemainderBound_proved

end

end RiemannHypothesisProject.Experiments.M100
