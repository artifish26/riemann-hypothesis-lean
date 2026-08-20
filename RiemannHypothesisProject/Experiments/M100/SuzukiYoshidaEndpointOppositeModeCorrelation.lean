import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointOppositeModeReduction
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaPrimeTranslationEntries

/-!
# Physical correlation of opposite endpoint modes

This module evaluates the symmetric physical translation correlation of the
endpoint exponentials with frequencies `n` and `-n`.  The calculation is
obtained from the already checked diagonal cosine and sine correlations by the
unitary two-mode change of coordinates.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

/-- The real symmetric cross-correlation of opposite exponentials is the
difference between the positive even and odd diagonal correlations. -/
theorem re_suzukiL2SymmetricTranslationEnergy_exponential_opposite_eq
    {r : Real} (hr : 0 < r) (t : Real) (n : Nat) (hn : 0 < n) :
    (suzukiL2SymmetricTranslationEnergy t
      (suzukiYoshidaExponentialL2 r hr (n : Int))
      (suzukiYoshidaExponentialL2 r hr (-(n : Int)))).re =
        (inner Complex
          (suzukiL2TranslateCLM t (suzukiYoshidaEvenL2 r hr n))
          (suzukiYoshidaEvenL2 r hr n)).re -
        (inner Complex
          (suzukiL2TranslateCLM t (suzukiYoshidaOddL2 r hr n))
          (suzukiYoshidaOddL2 r hr n)).re := by
  unfold suzukiL2SymmetricTranslationEnergy
    suzukiYoshidaEvenL2 suzukiYoshidaOddL2
  rw [dif_neg hn.ne']
  have hsqrtTwoSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hevenCoeff :
      star (((Real.sqrt 2)⁻¹ : Complex)) *
          (((Real.sqrt 2)⁻¹ : Complex)) = ((2 : Real)⁻¹ : Complex) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_inv, Complex.normSq_ofReal]
    norm_cast
    simpa [pow_two] using congrArg Inv.inv hsqrtTwoSq
  have hoddCoeff :
      star (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
          (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) =
        ((2 : Real)⁻¹ : Complex) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_inv, Complex.normSq_mul, Complex.normSq_I,
      Complex.normSq_ofReal]
    norm_cast
    simpa [pow_two] using congrArg Inv.inv hsqrtTwoSq
  have hevenCoeff' :
      (((Real.sqrt 2)⁻¹ : Complex)) *
          star (((Real.sqrt 2)⁻¹ : Complex)) = ((2 : Real)⁻¹ : Complex) := by
    simpa [mul_comm] using hevenCoeff
  have hoddCoeff' :
      (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
          star (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) =
        ((2 : Real)⁻¹ : Complex) := by
    simpa [mul_comm] using hoddCoeff
  simp only [map_smul, map_add, map_sub,
    inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, starRingEnd_apply, mul_add, mul_sub,
    ← mul_assoc]
  rw [hevenCoeff', hoddCoeff']
  norm_num
  ring_nf
  congr 1
  rw [← inner_conj_symm, starRingEnd_apply, Complex.star_def,
    Complex.conj_re]

/-- On the overlap range, the symmetric physical correlation of opposite
endpoint modes is the expected sine kernel. -/
theorem re_suzukiL2SymmetricTranslationEnergy_exponential_opposite
    {r t : Real} (hr : 0 < r) (ht0 : 0 ≤ t) (ht : t ≤ 2 * r)
    (n : Nat) (hn : 0 < n) :
    (suzukiL2SymmetricTranslationEnergy t
      (suzukiYoshidaExponentialL2 r hr (n : Int))
      (suzukiYoshidaExponentialL2 r hr (-(n : Int)))).re =
      -Real.sin (((n : Real) * Real.pi / r) * t) /
        ((n : Real) * Real.pi) := by
  rw [re_suzukiL2SymmetricTranslationEnergy_exponential_opposite_eq
    hr t n hn]
  simp only [suzukiL2TranslateCLM_apply]
  rw [inner_suzukiL2Translate_evenPositive_eq_correlation
      hr ht0 ht n hn,
    inner_suzukiL2Translate_odd_eq_correlation
      hr ht0 ht n hn]
  simp only [Complex.ofReal_re]
  have hnReal : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hr.ne', hnReal, Real.pi_ne_zero]
  ring

end

end RiemannHypothesisProject.Experiments.M100
