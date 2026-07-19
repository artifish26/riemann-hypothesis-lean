import RiemannHypothesisProject.LiCriterion.ZetaFunctionalMultiplicityReflection

/-!
# Lagarias's rational Li basis

The integer-indexed rational tests are
`G_n(s) = 1 - (1 - 1 / s)^n`.  They are kept separate from the ordinary
Schwartz trace class because every nonzero member has a pole at `0` or `1`.
This module proves the two algebraic identities used by Lagarias's Weil
pairing theorem.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open ComplexConjugate

noncomputable section

/-- Lagarias's integer-indexed rational Li test `G_n`. -/
def liRationalTest (n : Int) (s : Complex) : Complex :=
  1 - (1 - s⁻¹) ^ n

@[simp]
theorem liRationalTest_zero (s : Complex) :
    liRationalTest 0 s = 0 := by
  simp [liRationalTest]

/-- The nonnegative-index rational test is the M50 complex Li summand. -/
theorem liRationalTest_ofNat (n : Nat) (s : Complex) :
    liRationalTest (n : Int) s = zetaLiComplexSummand s n := by
  simp [liRationalTest, zetaLiComplexSummand]

/-- The Mobius ratio at `1 - s` is the inverse of the ratio at `s`. -/
theorem liRationalRatio_one_sub
    {s : Complex} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    1 - (1 - s)⁻¹ = (1 - s⁻¹)⁻¹ := by
  have h_one_sub : 1 - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
  have h_sub_one : s - 1 ≠ 0 := sub_ne_zero.mpr hs₁
  field_simp [hs₀, h_one_sub, h_sub_one]
  ring

/-- Lagarias's reflection identity `G_{-n}(s) = G_n(1 - s)`. -/
theorem liRationalTest_neg
    (n : Int) {s : Complex} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    liRationalTest (-n) s = liRationalTest n (1 - s) := by
  rw [liRationalTest, liRationalTest,
    liRationalRatio_one_sub hs₀ hs₁, inv_zpow, zpow_neg]

/-- The Mobius ratio is nonzero away from the endpoint `1`. -/
theorem liRationalRatio_ne_zero
    {s : Complex} (hs₁ : s ≠ 1) :
    1 - s⁻¹ ≠ 0 := by
  intro h
  have hinv : s⁻¹ = 1 := (sub_eq_zero.mp h).symm
  exact hs₁ (inv_eq_one.mp hinv)

/-- Lagarias's product identity
`G_n G_{-m} = G_n + G_{-m} - G_{n-m}`. -/
theorem liRationalTest_mul_neg
    (n m : Int) {s : Complex} (hs₁ : s ≠ 1) :
    liRationalTest n s * liRationalTest (-m) s =
      liRationalTest n s + liRationalTest (-m) s -
        liRationalTest (n - m) s := by
  have hratio : 1 - s⁻¹ ≠ 0 := liRationalRatio_ne_zero hs₁
  rw [liRationalTest, liRationalTest, liRationalTest]
  rw [zpow_neg, zpow_sub₀ hratio]
  field_simp
  ring

/-- Complex conjugation commutes with every integer-indexed rational test. -/
theorem liRationalTest_conj (n : Int) (s : Complex) :
    liRationalTest n (conj s) = conj (liRationalTest n s) := by
  simp [liRationalTest]

/-- The conjugated second factor in the Weil pairing is `G_{-m}`. -/
theorem conj_liRationalTest_one_sub_conj
    (m : Int) {s : Complex} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    conj (liRationalTest m (1 - conj s)) = liRationalTest (-m) s := by
  calc
    conj (liRationalTest m (1 - conj s)) =
        liRationalTest m (1 - s) := by
      rw [← liRationalTest_conj]
      simp
    _ = liRationalTest (-m) s :=
      (liRationalTest_neg m hs₀ hs₁).symm

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
