import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaZeroPairingSummability

/-!
# M100-DF6F diagonal energy to bounded source form

This module isolates the quantitative analytic input needed for boundedness of
the literal equation-(3.1) localized Weil form.  A single diagonal
multiplicity-weighted square estimate supplies all polarized summability and,
through a scaling argument, the product norm bound required by the transported
real-bilinear form interface.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- Absolute convergence and the pointwise diagonal majorant control the norm
of the full polarized zeta Weil pairing by the two diagonal energies. -/
theorem norm_zetaWeilPairing_le_tsum_normSq_add
    (F G : Complex → Complex)
    (hF : Summable (zetaWeilNormSqSummand F))
    (hG : Summable (zetaWeilNormSqSummand G)) :
    norm (zetaWeilPairing F G) ≤
      (∑' rho, zetaWeilNormSqSummand F rho) +
        ∑' rho, zetaWeilNormSqSummand G rho := by
  have hGReflection : Summable
      (fun rho : PositiveOrdinateZetaZeroSubtype ↦
        zetaWeilNormSqSummand G
          (positiveOrdinateZetaZeroFunctionalReflection rho)) :=
    positiveOrdinateZetaZeroFunctionalReflectionEquiv.summable_iff.mpr hG
  have hPair : Summable (zetaWeilPairingSummand F G) :=
    summable_zetaWeilPairingSummand_of_normSq F G hF hG
  calc
    norm (zetaWeilPairing F G) ≤
        ∑' rho, norm (zetaWeilPairingSummand F G rho) := by
      exact norm_tsum_le_tsum_norm hPair.norm
    _ ≤ ∑' rho, (zetaWeilNormSqSummand F rho +
        zetaWeilNormSqSummand G
          (positiveOrdinateZetaZeroFunctionalReflection rho)) := by
      exact hPair.norm.tsum_le_tsum
        (norm_zetaWeilPairingSummand_le_normSq_add_reflection F G)
        (hF.add hGReflection)
    _ = (∑' rho, zetaWeilNormSqSummand F rho) +
        ∑' rho, zetaWeilNormSqSummand G rho := by
      rw [hF.tsum_add hGReflection]
      exact congrArg
        (fun x : Real ↦ (∑' rho, zetaWeilNormSqSummand F rho) + x)
        (positiveOrdinateZetaZeroFunctionalReflectionEquiv.tsum_eq
          (zetaWeilNormSqSummand G))

/-- Additivity in the second argument for two explicitly summable pairing
families. -/
theorem zetaWeilPairing_add_right
    (F G H : Complex → Complex)
    (hG : Summable (zetaWeilPairingSummand F G))
    (hH : Summable (zetaWeilPairingSummand F H)) :
    zetaWeilPairing F (fun s => G s + H s) =
      zetaWeilPairing F G + zetaWeilPairing F H := by
  rw [zetaWeilPairing, zetaWeilPairing, zetaWeilPairing]
  rw [← hG.tsum_add hH]
  apply tsum_congr
  intro rho
  simp [zetaWeilPairingSummand]
  ring

end


end ComplexCompactExhaustion

namespace Experiments.M100

noncomputable section

open ComplexConjugate

/-- The literal transform after transport from the completed source-form
domain. -/
abbrev suzukiSourceAaLocalizedWeilTransform
    (u : SuzukiYoshidaCorrectedCommonFormDomain) : Complex → Complex :=
  suzukiSourceWeilTransform suzukiProjectAStar
    (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)

theorem suzukiSourceAaLocalizedWeilTransform_add
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiSourceAaLocalizedWeilTransform (u + v) =
      fun rho ↦ suzukiSourceAaLocalizedWeilTransform u rho +
        suzukiSourceAaLocalizedWeilTransform v rho := by
  funext rho
  unfold suzukiSourceAaLocalizedWeilTransform suzukiSourceWeilTransform
  rw [map_add]
  exact suzukiFiniteIntervalFourierValue_add _ _ _ _

theorem suzukiSourceAaLocalizedWeilTransform_smul
    (c : Complex) (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiSourceAaLocalizedWeilTransform (c • u) =
      fun rho ↦ c * suzukiSourceAaLocalizedWeilTransform u rho := by
  funext rho
  unfold suzukiSourceAaLocalizedWeilTransform suzukiSourceWeilTransform
  rw [map_smul]
  exact suzukiFiniteIntervalFourierValue_smul _ _ _ _

/-- The exact remaining quantitative diagonal source theorem.  Summability is
included explicitly because the totalized `tsum` alone does not record it. -/
def SuzukiSourceAaLocalizedWeilDiagonalBound : Prop :=
  ∃ C : Real, 0 < C ∧
    ∀ u : SuzukiYoshidaCorrectedCommonFormDomain,
      Summable (ComplexCompactExhaustion.zetaWeilNormSqSummand
        (suzukiSourceAaLocalizedWeilTransform u)) ∧
      (∑' rho, ComplexCompactExhaustion.zetaWeilNormSqSummand
        (suzukiSourceAaLocalizedWeilTransform u) rho) ≤ C * ‖u‖ ^ 2

/-- The quantitative diagonal estimate contains the previously isolated
qualitative diagonal summability condition. -/
theorem suzukiSourceAaLocalizedWeilNormSqSummable_of_diagonalBound
    (hdiag : SuzukiSourceAaLocalizedWeilDiagonalBound) :
    SuzukiSourceAaLocalizedWeilNormSqSummable := by
  obtain ⟨C, hC, hdiag⟩ := hdiag
  intro u
  exact (hdiag u).1

/-- Consequently the quantitative diagonal estimate supplies genuine
summability of every polarized source pairing. -/
theorem suzukiSourceAaLocalizedWeilPairingSummable_of_diagonalBound
    (hdiag : SuzukiSourceAaLocalizedWeilDiagonalBound) :
    SuzukiSourceAaLocalizedWeilPairingSummable :=
  suzukiSourceAaLocalizedWeilPairingSummable_of_normSq
    (suzukiSourceAaLocalizedWeilNormSqSummable_of_diagonalBound hdiag)

theorem suzukiSourceAaLocalizedWeilForm_add_left_of_diagonalBound
    (hdiag : SuzukiSourceAaLocalizedWeilDiagonalBound)
    (u₁ u₂ v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiSourceAaLocalizedWeilForm (u₁ + u₂) v =
      suzukiSourceAaLocalizedWeilForm u₁ v +
        suzukiSourceAaLocalizedWeilForm u₂ v := by
  change ComplexCompactExhaustion.zetaWeilPairing
      (suzukiSourceAaLocalizedWeilTransform v)
      (suzukiSourceAaLocalizedWeilTransform (u₁ + u₂)) =
    ComplexCompactExhaustion.zetaWeilPairing
        (suzukiSourceAaLocalizedWeilTransform v)
        (suzukiSourceAaLocalizedWeilTransform u₁) +
      ComplexCompactExhaustion.zetaWeilPairing
        (suzukiSourceAaLocalizedWeilTransform v)
        (suzukiSourceAaLocalizedWeilTransform u₂)
  rw [suzukiSourceAaLocalizedWeilTransform_add]
  exact ComplexCompactExhaustion.zetaWeilPairing_add_right _ _ _
    ((suzukiSourceAaLocalizedWeilPairingSummable_of_diagonalBound hdiag) v u₁)
    ((suzukiSourceAaLocalizedWeilPairingSummable_of_diagonalBound hdiag) v u₂)

theorem suzukiSourceAaLocalizedWeilForm_smul_left
    (c : Complex) (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiSourceAaLocalizedWeilForm (c • u) v =
      conj c * suzukiSourceAaLocalizedWeilForm u v := by
  change ComplexCompactExhaustion.zetaWeilPairing
      (suzukiSourceAaLocalizedWeilTransform v)
      (suzukiSourceAaLocalizedWeilTransform (c • u)) =
    conj c * ComplexCompactExhaustion.zetaWeilPairing
      (suzukiSourceAaLocalizedWeilTransform v)
      (suzukiSourceAaLocalizedWeilTransform u)
  rw [suzukiSourceAaLocalizedWeilTransform_smul]
  exact ComplexCompactExhaustion.zetaWeilPairing_mul_right _ _ _

theorem suzukiSourceAaLocalizedWeilForm_add_right_of_diagonalBound
    (hdiag : SuzukiSourceAaLocalizedWeilDiagonalBound)
    (u v₁ v₂ : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiSourceAaLocalizedWeilForm u (v₁ + v₂) =
      suzukiSourceAaLocalizedWeilForm u v₁ +
        suzukiSourceAaLocalizedWeilForm u v₂ := by
  calc
    suzukiSourceAaLocalizedWeilForm u (v₁ + v₂) =
        conj (suzukiSourceAaLocalizedWeilForm (v₁ + v₂) u) :=
      suzukiSourceAaLocalizedWeilForm_conj_symm u (v₁ + v₂)
    _ = conj (suzukiSourceAaLocalizedWeilForm v₁ u +
        suzukiSourceAaLocalizedWeilForm v₂ u) := by
      rw [suzukiSourceAaLocalizedWeilForm_add_left_of_diagonalBound
        hdiag v₁ v₂ u]
    _ = suzukiSourceAaLocalizedWeilForm u v₁ +
        suzukiSourceAaLocalizedWeilForm u v₂ := by
      rw [map_add]
      rw [← suzukiSourceAaLocalizedWeilForm_conj_symm,
        ← suzukiSourceAaLocalizedWeilForm_conj_symm]

theorem suzukiSourceAaLocalizedWeilForm_smul_right
    (c : Complex) (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiSourceAaLocalizedWeilForm u (c • v) =
      c * suzukiSourceAaLocalizedWeilForm u v := by
  change ComplexCompactExhaustion.zetaWeilPairing
      (suzukiSourceAaLocalizedWeilTransform (c • v))
      (suzukiSourceAaLocalizedWeilTransform u) =
    c * ComplexCompactExhaustion.zetaWeilPairing
      (suzukiSourceAaLocalizedWeilTransform v)
      (suzukiSourceAaLocalizedWeilTransform u)
  rw [suzukiSourceAaLocalizedWeilTransform_smul]
  exact ComplexCompactExhaustion.zetaWeilPairing_mul_left _ _ _

/-- Before scaling, the literal polarized form is controlled by the sum of
the two diagonal zero energies. -/
theorem norm_suzukiSourceAaLocalizedWeilForm_le_diagonal_add
    (hdiag : SuzukiSourceAaLocalizedWeilDiagonalBound)
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    norm (suzukiSourceAaLocalizedWeilForm u v) ≤
      (∑' rho, ComplexCompactExhaustion.zetaWeilNormSqSummand
        (suzukiSourceAaLocalizedWeilTransform u) rho) +
      ∑' rho, ComplexCompactExhaustion.zetaWeilNormSqSummand
        (suzukiSourceAaLocalizedWeilTransform v) rho := by
  obtain ⟨C, hC, hdiag⟩ := hdiag
  change norm (ComplexCompactExhaustion.zetaWeilPairing
      (suzukiSourceAaLocalizedWeilTransform v)
      (suzukiSourceAaLocalizedWeilTransform u)) ≤ _
  calc
    norm (ComplexCompactExhaustion.zetaWeilPairing
        (suzukiSourceAaLocalizedWeilTransform v)
        (suzukiSourceAaLocalizedWeilTransform u)) ≤
        (∑' rho, ComplexCompactExhaustion.zetaWeilNormSqSummand
          (suzukiSourceAaLocalizedWeilTransform v) rho) +
        ∑' rho, ComplexCompactExhaustion.zetaWeilNormSqSummand
          (suzukiSourceAaLocalizedWeilTransform u) rho :=
      ComplexCompactExhaustion.norm_zetaWeilPairing_le_tsum_normSq_add
        _ _ (hdiag v).1 (hdiag u).1
    _ = _ := add_comm _ _

/-- The diagonal energy estimate implies the product norm bound required of
the transported form.  The proof scales `u` by `‖v‖` and `v` by `‖u‖`, so
both diagonal estimates have the same quadratic norm factor. -/
theorem norm_suzukiSourceAaLocalizedWeilForm_le_of_diagonalBound
    (hdiag : SuzukiSourceAaLocalizedWeilDiagonalBound)
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    norm (suzukiSourceAaLocalizedWeilForm u v) ≤
      2 * hdiag.choose * ‖u‖ * ‖v‖ := by
  by_cases hu : u = 0
  · subst u
    have hzero := suzukiSourceAaLocalizedWeilForm_smul_left
      (0 : Complex) (0 : SuzukiYoshidaCorrectedCommonFormDomain) v
    have hformZero : suzukiSourceAaLocalizedWeilForm 0 v = 0 := by
      simpa using hzero
    simp [hformZero]
  by_cases hv : v = 0
  · subst v
    have hzero := suzukiSourceAaLocalizedWeilForm_smul_right
      (0 : Complex) u (0 : SuzukiYoshidaCorrectedCommonFormDomain)
    have hformZero : suzukiSourceAaLocalizedWeilForm u 0 = 0 := by
      simpa using hzero
    simp [hformZero]
  let C : Real := hdiag.choose
  have hC : 0 < C := hdiag.choose_spec.1
  have hdiag' := hdiag.choose_spec.2
  let ur : SuzukiYoshidaCorrectedCommonFormDomain := (‖v‖ : Complex) • u
  let vr : SuzukiYoshidaCorrectedCommonFormDomain := (‖u‖ : Complex) • v
  have hnorm := norm_suzukiSourceAaLocalizedWeilForm_le_diagonal_add
    hdiag ur vr
  have henergyU := (hdiag' ur).2
  have henergyV := (hdiag' vr).2
  have hscaled :
      norm (suzukiSourceAaLocalizedWeilForm ur vr) ≤
        C * ‖ur‖ ^ 2 + C * ‖vr‖ ^ 2 :=
    hnorm.trans (add_le_add henergyU henergyV)
  have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hvNorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hurNorm : ‖ur‖ = ‖v‖ * ‖u‖ := by
    change ‖(‖v‖ : Complex) •
        (u : SuzukiLogHilbertGraphSpace)‖ = ‖v‖ * ‖u‖
    rw [norm_smul]
    simp
  have hvrNorm : ‖vr‖ = ‖u‖ * ‖v‖ := by
    change ‖(‖u‖ : Complex) •
        (v : SuzukiLogHilbertGraphSpace)‖ = ‖u‖ * ‖v‖
    rw [norm_smul]
    simp
  have hformScaled :
      suzukiSourceAaLocalizedWeilForm ur vr =
        ((‖v‖ : Complex) * (‖u‖ : Complex)) *
          suzukiSourceAaLocalizedWeilForm u v := by
    rw [show ur = (‖v‖ : Complex) • u from rfl,
      show vr = (‖u‖ : Complex) • v from rfl,
      suzukiSourceAaLocalizedWeilForm_smul_left,
      suzukiSourceAaLocalizedWeilForm_smul_right]
    simp
    ring
  have hvComplexNorm : ‖(‖v‖ : Complex)‖ = ‖v‖ := by simp
  have huComplexNorm : ‖(‖u‖ : Complex)‖ = ‖u‖ := by simp
  rw [hformScaled, norm_mul, norm_mul, hvComplexNorm,
    huComplexNorm, hurNorm, hvrNorm] at hscaled
  change norm (suzukiSourceAaLocalizedWeilForm u v) ≤
    2 * C * ‖u‖ * ‖v‖
  refine le_of_mul_le_mul_left ?_ (mul_pos hvNorm huNorm)
  calc
    (‖v‖ * ‖u‖) * norm (suzukiSourceAaLocalizedWeilForm u v) ≤
        C * (‖v‖ * ‖u‖) ^ 2 + C * (‖u‖ * ‖v‖) ^ 2 := hscaled
    _ = (‖v‖ * ‖u‖) * (2 * C * ‖u‖ * ‖v‖) := by ring

/-- The single diagonal source estimate supplies the complete bounded
real-bilinear interface for the literal transported Weil form. -/
theorem suzukiSourceAaLocalizedWeilForm_boundedRealBilinear_of_diagonalBound
    (hdiag : SuzukiSourceAaLocalizedWeilDiagonalBound) :
    SuzukiSourceAaClosedFormBoundedRealBilinear
      suzukiSourceAaLocalizedWeilForm := by
  refine
    { add_left := ?_
      smul_left := ?_
      add_right := ?_
      smul_right := ?_
      bound := ?_ }
  · intro u₁ u₂ v
    exact suzukiSourceAaLocalizedWeilForm_add_left_of_diagonalBound
      hdiag u₁ u₂ v
  · intro c u v
    change suzukiSourceAaLocalizedWeilForm (c • u) v =
      c • suzukiSourceAaLocalizedWeilForm u v
    have hcu : c • u = (c : Complex) • u := by
      apply Subtype.ext
      exact RCLike.real_smul_eq_coe_smul (K := Complex) c
        (u : SuzukiLogHilbertGraphSpace)
    rw [hcu, RCLike.real_smul_eq_coe_mul]
    simpa using
      suzukiSourceAaLocalizedWeilForm_smul_left (c : Complex) u v
  · intro u v₁ v₂
    exact suzukiSourceAaLocalizedWeilForm_add_right_of_diagonalBound
      hdiag u v₁ v₂
  · intro c u v
    change suzukiSourceAaLocalizedWeilForm u (c • v) =
      c • suzukiSourceAaLocalizedWeilForm u v
    have hcv : c • v = (c : Complex) • v := by
      apply Subtype.ext
      exact RCLike.real_smul_eq_coe_smul (K := Complex) c
        (v : SuzukiLogHilbertGraphSpace)
    rw [hcv, RCLike.real_smul_eq_coe_mul]
    simpa using
      suzukiSourceAaLocalizedWeilForm_smul_right (c : Complex) u v
  · refine ⟨2 * hdiag.choose, mul_pos (by norm_num) hdiag.choose_spec.1, ?_⟩
    intro u v
    exact norm_suzukiSourceAaLocalizedWeilForm_le_of_diagonalBound hdiag u v

/-- Hence the quantitative diagonal estimate is the sole remaining input for
the existing literal-form boundedness premise: it provides both honest
cross-pair summability and bounded real bilinearity. -/
theorem suzukiSourceAaLocalizedWeilFormBounded_of_diagonalBound
    (hdiag : SuzukiSourceAaLocalizedWeilDiagonalBound) :
    SuzukiSourceAaLocalizedWeilFormBounded :=
  ⟨suzukiSourceAaLocalizedWeilPairingSummable_of_diagonalBound hdiag,
    suzukiSourceAaLocalizedWeilForm_boundedRealBilinear_of_diagonalBound
      hdiag⟩

end


end Experiments.M100

end RiemannHypothesisProject
