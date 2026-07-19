import RiemannHypothesisProject.RiemannVonMangoldt.BellottiWongGammaEndpointBounds

/-!
# Finite certificate for Bennett's compact Gamma interval

This module contains the concrete rational leaves for the compact interval
`[5/7,8]`.  Each leaf is checked from rational arithmetic plus mathlib's
certified enclosures of `pi`, `log 2`, and `log 3`.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- Builds a checked rational leaf below the `g11` critical height. -/
def bennettGammaIncreasingRationalLeaf
    (a b r : Real) (lowerInverse upperInverse : Bool)
    (lowerTwo lowerThree upperTwo upperThree : Nat)
    (ha : 0 < a) (hab : a <= b) (hcritical : 8 * b ^ 2 <= 81)
    (hr : 0 <= r)
    (hrsq : (32 * b) ^ 2 <= r ^ 2 * (81 + 4 * b ^ 2) ^ 3)
    (valid : BennettGammaRationalIntervalBoxValid r lowerInverse upperInverse
      lowerTwo lowerThree upperTwo upperThree a b)
    (hlowerRange : BennettGammaMixedLogScaleValid lowerInverse
      lowerTwo lowerThree (1 + 81 / (4 * a ^ 2)))
    (hupperRange : BennettGammaMixedLogScaleValid upperInverse
      upperTwo upperThree (1 + 81 / (4 * b ^ 2))) :
    BennettGammaScaledIntervalCertificate a b := by
  apply BennettGammaScaledIntervalCertificate.box r
  · intro T haT hTb
    exact (bennettGammaIntervalRpowComponent_le_right_endpoint
      ha.le hab hcritical haT hTb).trans
        (bennettGammaIntervalRpowComponent_le_of_sq (ha.le.trans hab) hr hrsq)
  · exact valid.toScaled ha (ha.trans_le hab) hlowerRange hupperRange

/-- Builds a checked rational leaf above the `g11` critical height. -/
def bennettGammaDecreasingRationalLeaf
    (a b r : Real) (lowerInverse upperInverse : Bool)
    (lowerTwo lowerThree upperTwo upperThree : Nat)
    (ha : 0 < a) (hab : a <= b) (hcritical : 81 <= 8 * a ^ 2)
    (hr : 0 <= r)
    (hrsq : (32 * a) ^ 2 <= r ^ 2 * (81 + 4 * a ^ 2) ^ 3)
    (valid : BennettGammaRationalIntervalBoxValid r lowerInverse upperInverse
      lowerTwo lowerThree upperTwo upperThree a b)
    (hlowerRange : BennettGammaMixedLogScaleValid lowerInverse
      lowerTwo lowerThree (1 + 81 / (4 * a ^ 2)))
    (hupperRange : BennettGammaMixedLogScaleValid upperInverse
      upperTwo upperThree (1 + 81 / (4 * b ^ 2))) :
    BennettGammaScaledIntervalCertificate a b := by
  apply BennettGammaScaledIntervalCertificate.box r
  · intro T haT hTb
    exact (bennettGammaIntervalRpowComponent_le_left_endpoint
      ha.le hcritical haT hTb).trans
        (bennettGammaIntervalRpowComponent_le_of_sq ha.le hr hrsq)
  · exact valid.toScaled ha (ha.trans_le hab) hlowerRange hupperRange

/--
Builds a checked rational leaf crossing the unique `g11` critical height.
The sharp endpoint constructors cannot span that point, so this one uses the
global `8/81` majorant proved in the interval-box module.
-/
def bennettGammaUniformRationalLeaf
    (a b : Real) (lowerInverse upperInverse : Bool)
    (lowerTwo lowerThree upperTwo upperThree : Nat)
    (ha : 0 < a) (hab : a <= b)
    (valid : BennettGammaRationalIntervalBoxValid (8 / 81)
      lowerInverse upperInverse lowerTwo lowerThree upperTwo upperThree a b)
    (hlowerRange : BennettGammaMixedLogScaleValid lowerInverse
      lowerTwo lowerThree (1 + 81 / (4 * a ^ 2)))
    (hupperRange : BennettGammaMixedLogScaleValid upperInverse
      upperTwo upperThree (1 + 81 / (4 * b ^ 2))) :
    BennettGammaScaledIntervalCertificate a b := by
  apply BennettGammaScaledIntervalCertificate.box (8 / 81)
  · intro T haT _
    exact bennettGammaIntervalRpowComponent_le_eight_div_eightyOne
      (ha.trans_le haT)
  · exact valid.toScaled ha (ha.trans_le hab) hlowerRange hupperRange

private theorem firstLeafRpowBound :
    ∀ T : Real, (5 : Real) / 7 <= T -> T <= 1429 / 2000 ->
      bennettGammaIntervalRpowComponent T <= 31 / 1000 := by
  intro T hleft hright
  have hendpoint := bennettGammaIntervalRpowComponent_le_right_endpoint
    (a := (5 : Real) / 7) (b := (1429 : Real) / 2000) (T := T)
    (by norm_num) (by norm_num) (by norm_num) hleft hright
  apply hendpoint.trans
  apply bennettGammaIntervalRpowComponent_le_of_sq (by norm_num) (by norm_num)
  norm_num

private theorem firstLeafRationalValid :
    BennettGammaRationalIntervalBoxValid
      (31 / 1000 : Real) false false 2 2 2 2
        ((5 : Real) / 7) (1429 / 2000) := by
  unfold BennettGammaRationalIntervalBoxValid
    bennettGammaRationalLowerIntervalBox
    bennettGammaRationalUpperIntervalBox
    bennettGammaIntervalRationalComponent
    bennettGammaArctanEndpointLower
    bennettGammaArctanEndpointUpper
    bennettGammaMixedLogEndpointLowerWithMode
    bennettGammaMixedLogEndpointUpperWithMode
    bennettGammaMixedLogEndpointLower
    bennettGammaMixedLogEndpointUpper
    arctanSepticPolynomial
    arctanNonicPolynomial
    logQuarticPolynomial
    logQuinticPolynomial
  norm_num
  constructor <;>
    field_simp [Real.pi_pos.ne'] <;>
      nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem firstLeafValid :
    BennettGammaScaledIntervalBoxValid
      (31 / 1000 : Real) ((5 : Real) / 7) (1429 / 2000) := by
  apply firstLeafRationalValid.toScaled (by norm_num) (by norm_num)
  · norm_num [BennettGammaMixedLogScaleValid]
  · norm_num [BennettGammaMixedLogScaleValid]

/-- The first outward-rounded leaf at the lower endpoint. -/
def bennettGammaFirstFiniteCertificateLeaf :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (1429 / 2000) :=
  .box (31 / 1000) firstLeafRpowBound firstLeafValid

private theorem secondLeafRationalValid :
    BennettGammaRationalIntervalBoxValid
      (30223 / 1000000 : Real) false false 2 2 2 2
        (1429 / 2000) (357361 / 500000) := by
  norm_num [BennettGammaRationalIntervalBoxValid,
    bennettGammaRationalLowerIntervalBox,
    bennettGammaRationalUpperIntervalBox,
    bennettGammaIntervalRationalComponent,
    bennettGammaArctanEndpointLower,
    bennettGammaArctanEndpointUpper,
    bennettGammaMixedLogEndpointLowerWithMode,
    bennettGammaMixedLogEndpointUpperWithMode,
    bennettGammaMixedLogEndpointLower,
    bennettGammaMixedLogEndpointUpper,
    arctanSepticPolynomial,
    arctanNonicPolynomial,
    logQuarticPolynomial,
    logQuinticPolynomial]
  constructor <;>
    field_simp [Real.pi_pos.ne'] <;>
      nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

/-- The second outward-rounded leaf, built by the reusable rational constructor. -/
def bennettGammaSecondFiniteCertificateLeaf :
    BennettGammaScaledIntervalCertificate (1429 / 2000) (357361 / 500000) := by
  exact bennettGammaIncreasingRationalLeaf
    (1429 / 2000) (357361 / 500000) (30223 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    secondLeafRationalValid
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- The first two adjacent leaves assembled by the certificate split rule. -/
def bennettGammaFirstTwoFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (357361 / 500000) :=
  .split (1429 / 2000) (by norm_num) (by norm_num)
    bennettGammaFirstFiniteCertificateLeaf bennettGammaSecondFiniteCertificateLeaf

private theorem thirdLeafRationalValid :
    BennettGammaRationalIntervalBoxValid
      (30231 / 1000000 : Real) false false 2 2 2 2
        (357361 / 500000) (28597 / 40000) := by
  norm_num [BennettGammaRationalIntervalBoxValid,
    bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
    bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
    bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
    bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
    bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
    arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
  constructor <;> field_simp [Real.pi_pos.ne'] <;>
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem fourthLeafRationalValid :
    BennettGammaRationalIntervalBoxValid
      (30239 / 1000000 : Real) false false 2 2 2 2
        (28597 / 40000) (715131 / 1000000) := by
  norm_num [BennettGammaRationalIntervalBoxValid,
    bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
    bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
    bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
    bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
    bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
    arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
  constructor <;> field_simp [Real.pi_pos.ne'] <;>
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem fifthLeafRationalValid :
    BennettGammaRationalIntervalBoxValid
      (30247 / 1000000 : Real) false false 2 2 2 2
        (715131 / 1000000) (35767 / 50000) := by
  norm_num [BennettGammaRationalIntervalBoxValid,
    bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
    bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
    bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
    bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
    bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
    arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
  constructor <;> field_simp [Real.pi_pos.ne'] <;>
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem sixthLeafRationalValid :
    BennettGammaRationalIntervalBoxValid
      (30255 / 1000000 : Real) false false 2 2 2 2
        (35767 / 50000) (22361 / 31250) := by
  norm_num [BennettGammaRationalIntervalBoxValid,
    bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
    bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
    bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
    bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
    bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
    arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
  constructor <;> field_simp [Real.pi_pos.ne'] <;>
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem seventhLeafRationalValid :
    BennettGammaRationalIntervalBoxValid
      (30264 / 1000000 : Real) false false 2 2 2 2
        (22361 / 31250) (715767 / 1000000) := by
  norm_num [BennettGammaRationalIntervalBoxValid,
    bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
    bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
    bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
    bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
    bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
    arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
  constructor <;> field_simp [Real.pi_pos.ne'] <;>
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def thirdLeaf :
    BennettGammaScaledIntervalCertificate (357361 / 500000) (28597 / 40000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30231 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    thirdLeafRationalValid
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fourthLeaf :
    BennettGammaScaledIntervalCertificate (28597 / 40000) (715131 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30239 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    fourthLeafRationalValid
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fifthLeaf :
    BennettGammaScaledIntervalCertificate (715131 / 1000000) (35767 / 50000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30247 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    fifthLeafRationalValid
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def sixthLeaf :
    BennettGammaScaledIntervalCertificate (35767 / 50000) (22361 / 31250) :=
  bennettGammaIncreasingRationalLeaf _ _ (30255 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sixthLeafRationalValid
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def seventhLeaf :
    BennettGammaScaledIntervalCertificate (22361 / 31250) (715767 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30264 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    seventhLeafRationalValid
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstSevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (715767 / 1000000) :=
  .split (357361 / 500000) (by norm_num) (by norm_num)
    bennettGammaFirstTwoFiniteCertificateLeaves
    (.split (28597 / 40000) (by norm_num) (by norm_num) thirdLeaf
      (.split (715131 / 1000000) (by norm_num) (by norm_num) fourthLeaf
        (.split (35767 / 50000) (by norm_num) (by norm_num) fifthLeaf
          (.split (22361 / 31250) (by norm_num) (by norm_num) sixthLeaf seventhLeaf))))

private theorem eighthLeafRationalValid :
    BennettGammaRationalIntervalBoxValid
      (30272 / 1000000 : Real) false false 2 2 2 2
        (715767 / 1000000) (143197 / 200000) := by
  norm_num [BennettGammaRationalIntervalBoxValid,
    bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
    bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
    bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
    bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
    bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
    arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
  constructor <;> field_simp [Real.pi_pos.ne'] <;>
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem ninthLeafRationalValid :
    BennettGammaRationalIntervalBoxValid
      (30281 / 1000000 : Real) false false 2 2 2 2
        (143197 / 200000) (358103 / 500000) := by
  norm_num [BennettGammaRationalIntervalBoxValid,
    bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
    bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
    bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
    bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
    bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
    arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
  constructor <;> field_simp [Real.pi_pos.ne'] <;>
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem tenthLeafRationalValid :
    BennettGammaRationalIntervalBoxValid
      (30290 / 1000000 : Real) false false 2 2 2 2
        (358103 / 500000) (716431 / 1000000) := by
  norm_num [BennettGammaRationalIntervalBoxValid,
    bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
    bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
    bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
    bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
    bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
    arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
  constructor <;> field_simp [Real.pi_pos.ne'] <;>
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem eleventhLeafRationalValid :
    BennettGammaRationalIntervalBoxValid
      (30299 / 1000000 : Real) false false 2 2 2 2
        (716431 / 1000000) (716659 / 1000000) := by
  norm_num [BennettGammaRationalIntervalBoxValid,
    bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
    bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
    bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
    bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
    bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
    arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
  constructor <;> field_simp [Real.pi_pos.ne'] <;>
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem twelfthLeafRationalValid :
    BennettGammaRationalIntervalBoxValid
      (30308 / 1000000 : Real) false false 2 2 2 2
        (716659 / 1000000) (71689 / 100000) := by
  norm_num [BennettGammaRationalIntervalBoxValid,
    bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
    bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
    bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
    bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
    bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
    arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
  constructor <;> field_simp [Real.pi_pos.ne'] <;>
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def eighthLeaf :
    BennettGammaScaledIntervalCertificate (715767 / 1000000) (143197 / 200000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30272 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    eighthLeafRationalValid
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def ninthLeaf :
    BennettGammaScaledIntervalCertificate (143197 / 200000) (358103 / 500000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30281 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ninthLeafRationalValid
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def tenthLeaf :
    BennettGammaScaledIntervalCertificate (358103 / 500000) (716431 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30290 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    tenthLeafRationalValid
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def eleventhLeaf :
    BennettGammaScaledIntervalCertificate (716431 / 1000000) (716659 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30299 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    eleventhLeafRationalValid
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twelfthLeaf :
    BennettGammaScaledIntervalCertificate (716659 / 1000000) (71689 / 100000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30308 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    twelfthLeafRationalValid
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Twelve checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstTwelveFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (71689 / 100000) :=
  .split (715767 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstSevenFiniteCertificateLeaves
    (.split (143197 / 200000) (by norm_num) (by norm_num) eighthLeaf
      (.split (358103 / 500000) (by norm_num) (by norm_num) ninthLeaf
        (.split (716431 / 1000000) (by norm_num) (by norm_num) tenthLeaf
          (.split (716659 / 1000000) (by norm_num) (by norm_num)
            eleventhLeaf twelfthLeaf))))

private theorem leavesThirteenThroughSeventeenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (30317 / 1000000 : Real) false false 2 2 2 2
          (71689 / 100000) (5737 / 8000) ∧
      BennettGammaRationalIntervalBoxValid
        (30326 / 1000000 : Real) false false 2 2 2 2
          (5737 / 8000) (717363 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30336 / 1000000 : Real) false false 2 2 2 2
          (717363 / 1000000) (179401 / 250000) ∧
      BennettGammaRationalIntervalBoxValid
        (30345 / 1000000 : Real) false false 2 2 2 2
          (179401 / 250000) (717849 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30355 / 1000000 : Real) false false 2 2 2 2
          (717849 / 1000000) (718097 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def thirteenthLeaf :
    BennettGammaScaledIntervalCertificate (71689 / 100000) (5737 / 8000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30317 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirteenThroughSeventeenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fourteenthLeaf :
    BennettGammaScaledIntervalCertificate (5737 / 8000) (717363 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30326 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirteenThroughSeventeenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fifteenthLeaf :
    BennettGammaScaledIntervalCertificate (717363 / 1000000) (179401 / 250000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30336 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirteenThroughSeventeenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def sixteenthLeaf :
    BennettGammaScaledIntervalCertificate (179401 / 250000) (717849 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30345 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirteenThroughSeventeenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def seventeenthLeaf :
    BennettGammaScaledIntervalCertificate (717849 / 1000000) (718097 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30355 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirteenThroughSeventeenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Seventeen checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstSeventeenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (718097 / 1000000) :=
  .split (71689 / 100000) (by norm_num) (by norm_num)
    bennettGammaFirstTwelveFiniteCertificateLeaves
    (.split (5737 / 8000) (by norm_num) (by norm_num) thirteenthLeaf
      (.split (717363 / 1000000) (by norm_num) (by norm_num) fourteenthLeaf
        (.split (179401 / 250000) (by norm_num) (by norm_num) fifteenthLeaf
          (.split (717849 / 1000000) (by norm_num) (by norm_num)
            sixteenthLeaf seventeenthLeaf))))

private theorem leavesEighteenThroughTwentyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (30365 / 1000000 : Real) false false 2 2 2 2
          (718097 / 1000000) (718349 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30375 / 1000000 : Real) false false 2 2 2 2
          (718349 / 1000000) (143721 / 200000) ∧
      BennettGammaRationalIntervalBoxValid
        (30385 / 1000000 : Real) false false 2 2 2 2
          (143721 / 200000) (44929 / 62500) ∧
      BennettGammaRationalIntervalBoxValid
        (30395 / 1000000 : Real) false false 2 2 2 2
          (44929 / 62500) (719127 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30406 / 1000000 : Real) false false 2 2 2 2
          (719127 / 1000000) (359697 / 500000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def eighteenthLeaf :
    BennettGammaScaledIntervalCertificate
      (718097 / 1000000) (718349 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30365 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEighteenThroughTwentyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def nineteenthLeaf :
    BennettGammaScaledIntervalCertificate
      (718349 / 1000000) (143721 / 200000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30375 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEighteenThroughTwentyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twentiethLeaf :
    BennettGammaScaledIntervalCertificate (143721 / 200000) (44929 / 62500) :=
  bennettGammaIncreasingRationalLeaf _ _ (30385 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEighteenThroughTwentyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twentyFirstLeaf :
    BennettGammaScaledIntervalCertificate (44929 / 62500) (719127 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30395 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEighteenThroughTwentyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twentySecondLeaf :
    BennettGammaScaledIntervalCertificate
      (719127 / 1000000) (359697 / 500000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30406 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEighteenThroughTwentyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Twenty-two checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstTwentyTwoFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate
      ((5 : Real) / 7) (359697 / 500000) :=
  .split (718097 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstSeventeenFiniteCertificateLeaves
    (.split (718349 / 1000000) (by norm_num) (by norm_num) eighteenthLeaf
      (.split (143721 / 200000) (by norm_num) (by norm_num) nineteenthLeaf
        (.split (44929 / 62500) (by norm_num) (by norm_num) twentiethLeaf
          (.split (719127 / 1000000) (by norm_num) (by norm_num)
            twentyFirstLeaf twentySecondLeaf))))

private theorem leavesTwentyThreeThroughTwentySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (30429 / 1000000 : Real) false false 2 2 2 2
          (359697 / 500000) (179999 / 250000) ∧
      BennettGammaRationalIntervalBoxValid
        (30454 / 1000000 : Real) false false 2 2 2 2
          (179999 / 250000) (720617 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30479 / 1000000 : Real) false false 2 2 2 2
          (720617 / 1000000) (360629 / 500000) ∧
      BennettGammaRationalIntervalBoxValid
        (30505 / 1000000 : Real) false false 2 2 2 2
          (360629 / 500000) (18048 / 25000) ∧
      BennettGammaRationalIntervalBoxValid
        (30531 / 1000000 : Real) false false 2 2 2 2
          (18048 / 25000) (722603 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def twentyThirdLeaf :
    BennettGammaScaledIntervalCertificate (359697 / 500000) (179999 / 250000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30429 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwentyThreeThroughTwentySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twentyFourthLeaf :
    BennettGammaScaledIntervalCertificate (179999 / 250000) (720617 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30454 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwentyThreeThroughTwentySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twentyFifthLeaf :
    BennettGammaScaledIntervalCertificate (720617 / 1000000) (360629 / 500000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30479 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwentyThreeThroughTwentySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twentySixthLeaf :
    BennettGammaScaledIntervalCertificate (360629 / 500000) (18048 / 25000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30505 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwentyThreeThroughTwentySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twentySeventhLeaf :
    BennettGammaScaledIntervalCertificate (18048 / 25000) (722603 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30531 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwentyThreeThroughTwentySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Twenty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstTwentySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (722603 / 1000000) :=
  .split (359697 / 500000) (by norm_num) (by norm_num)
    bennettGammaFirstTwentyTwoFiniteCertificateLeaves
    (.split (179999 / 250000) (by norm_num) (by norm_num) twentyThirdLeaf
      (.split (720617 / 1000000) (by norm_num) (by norm_num) twentyFourthLeaf
        (.split (360629 / 500000) (by norm_num) (by norm_num) twentyFifthLeaf
          (.split (18048 / 25000) (by norm_num) (by norm_num)
            twentySixthLeaf twentySeventhLeaf))))

private theorem leavesTwentyEightThroughThirtyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (30559 / 1000000 : Real) false false 2 2 2 2
          (722603 / 1000000) (723308 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30587 / 1000000 : Real) false false 2 2 2 2
          (723308 / 1000000) (724036 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30617 / 1000000 : Real) false false 2 2 2 2
          (724036 / 1000000) (724787 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30647 / 1000000 : Real) false false 2 2 2 2
          (724787 / 1000000) (725562 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30678 / 1000000 : Real) false false 2 2 2 2
          (725562 / 1000000) (726362 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesThirtyThreeThroughThirtySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (30710 / 1000000 : Real) false false 2 2 2 2
          (726362 / 1000000) (727188 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30743 / 1000000 : Real) false false 2 2 2 2
          (727188 / 1000000) (728040 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30778 / 1000000 : Real) false false 2 2 2 2
          (728040 / 1000000) (728920 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30813 / 1000000 : Real) false false 2 2 2 2
          (728920 / 1000000) (729828 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30850 / 1000000 : Real) false false 2 2 2 2
          (729828 / 1000000) (730765 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def twentyEighthLeaf :
    BennettGammaScaledIntervalCertificate (722603 / 1000000) (723308 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30559 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwentyEightThroughThirtyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twentyNinthLeaf :
    BennettGammaScaledIntervalCertificate (723308 / 1000000) (724036 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30587 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwentyEightThroughThirtyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def thirtiethLeaf :
    BennettGammaScaledIntervalCertificate (724036 / 1000000) (724787 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30617 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwentyEightThroughThirtyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def thirtyFirstLeaf :
    BennettGammaScaledIntervalCertificate (724787 / 1000000) (725562 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30647 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwentyEightThroughThirtyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def thirtySecondLeaf :
    BennettGammaScaledIntervalCertificate (725562 / 1000000) (726362 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30678 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwentyEightThroughThirtyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def thirtyThirdLeaf :
    BennettGammaScaledIntervalCertificate (726362 / 1000000) (727188 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30710 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirtyThreeThroughThirtySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def thirtyFourthLeaf :
    BennettGammaScaledIntervalCertificate (727188 / 1000000) (728040 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30743 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirtyThreeThroughThirtySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def thirtyFifthLeaf :
    BennettGammaScaledIntervalCertificate (728040 / 1000000) (728920 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30778 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirtyThreeThroughThirtySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def thirtySixthLeaf :
    BennettGammaScaledIntervalCertificate (728920 / 1000000) (729828 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30813 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirtyThreeThroughThirtySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def thirtySeventhLeaf :
    BennettGammaScaledIntervalCertificate (729828 / 1000000) (730765 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30850 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirtyThreeThroughThirtySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Thirty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstThirtySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (730765 / 1000000) :=
  .split (722603 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstTwentySevenFiniteCertificateLeaves
    (.split (723308 / 1000000) (by norm_num) (by norm_num) twentyEighthLeaf
      (.split (724036 / 1000000) (by norm_num) (by norm_num) twentyNinthLeaf
        (.split (724787 / 1000000) (by norm_num) (by norm_num) thirtiethLeaf
          (.split (725562 / 1000000) (by norm_num) (by norm_num) thirtyFirstLeaf
            (.split (726362 / 1000000) (by norm_num) (by norm_num) thirtySecondLeaf
              (.split (727188 / 1000000) (by norm_num) (by norm_num) thirtyThirdLeaf
                (.split (728040 / 1000000) (by norm_num) (by norm_num) thirtyFourthLeaf
                  (.split (728920 / 1000000) (by norm_num) (by norm_num) thirtyFifthLeaf
                    (.split (729828 / 1000000) (by norm_num) (by norm_num)
                      thirtySixthLeaf thirtySeventhLeaf)))))))))

private theorem leavesThirtyEightThroughFortyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (30887 / 1000000 : Real) false false 2 2 2 2
          (730765 / 1000000) (731733 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30926 / 1000000 : Real) false false 2 2 2 2
          (731733 / 1000000) (732732 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (30966 / 1000000 : Real) false false 2 2 2 2
          (732732 / 1000000) (733763 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31008 / 1000000 : Real) false false 2 2 2 2
          (733763 / 1000000) (734827 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31051 / 1000000 : Real) false false 2 2 2 2
          (734827 / 1000000) (735925 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesFortyThreeThroughFortySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (31095 / 1000000 : Real) false false 2 2 2 2
          (735925 / 1000000) (737059 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31140 / 1000000 : Real) false false 2 2 2 2
          (737059 / 1000000) (738229 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31187 / 1000000 : Real) false false 2 2 2 2
          (738229 / 1000000) (739437 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31235 / 1000000 : Real) false false 2 2 2 2
          (739437 / 1000000) (740684 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31285 / 1000000 : Real) false false 2 2 2 2
          (740684 / 1000000) (741971 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def thirtyEighthLeaf :
    BennettGammaScaledIntervalCertificate (730765 / 1000000) (731733 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30887 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirtyEightThroughFortyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def thirtyNinthLeaf :
    BennettGammaScaledIntervalCertificate (731733 / 1000000) (732732 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30926 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirtyEightThroughFortyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fortiethLeaf :
    BennettGammaScaledIntervalCertificate (732732 / 1000000) (733763 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (30966 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirtyEightThroughFortyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fortyFirstLeaf :
    BennettGammaScaledIntervalCertificate (733763 / 1000000) (734827 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31008 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirtyEightThroughFortyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fortySecondLeaf :
    BennettGammaScaledIntervalCertificate (734827 / 1000000) (735925 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31051 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesThirtyEightThroughFortyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fortyThirdLeaf :
    BennettGammaScaledIntervalCertificate (735925 / 1000000) (737059 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31095 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFortyThreeThroughFortySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fortyFourthLeaf :
    BennettGammaScaledIntervalCertificate (737059 / 1000000) (738229 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31140 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFortyThreeThroughFortySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fortyFifthLeaf :
    BennettGammaScaledIntervalCertificate (738229 / 1000000) (739437 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31187 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFortyThreeThroughFortySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fortySixthLeaf :
    BennettGammaScaledIntervalCertificate (739437 / 1000000) (740684 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31235 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFortyThreeThroughFortySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fortySeventhLeaf :
    BennettGammaScaledIntervalCertificate (740684 / 1000000) (741971 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31285 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFortyThreeThroughFortySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Forty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstFortySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (741971 / 1000000) :=
  .split (730765 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstThirtySevenFiniteCertificateLeaves
    (.split (731733 / 1000000) (by norm_num) (by norm_num) thirtyEighthLeaf
      (.split (732732 / 1000000) (by norm_num) (by norm_num) thirtyNinthLeaf
        (.split (733763 / 1000000) (by norm_num) (by norm_num) fortiethLeaf
          (.split (734827 / 1000000) (by norm_num) (by norm_num) fortyFirstLeaf
            (.split (735925 / 1000000) (by norm_num) (by norm_num) fortySecondLeaf
              (.split (737059 / 1000000) (by norm_num) (by norm_num) fortyThirdLeaf
                (.split (738229 / 1000000) (by norm_num) (by norm_num) fortyFourthLeaf
                  (.split (739437 / 1000000) (by norm_num) (by norm_num) fortyFifthLeaf
                    (.split (740684 / 1000000) (by norm_num) (by norm_num)
                      fortySixthLeaf fortySeventhLeaf)))))))))

private theorem leavesFortyEightThroughFiftyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (31337 / 1000000 : Real) false false 2 2 2 2
          (741971 / 1000000) (743299 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31390 / 1000000 : Real) false false 2 2 2 2
          (743299 / 1000000) (744670 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31445 / 1000000 : Real) false false 2 2 2 2
          (744670 / 1000000) (746085 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31503 / 1000000 : Real) false false 2 2 2 2
          (746085 / 1000000) (747546 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31560 / 1000000 : Real) false false 2 2 2 2
          (747546 / 1000000) (749054 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesFiftyThreeThroughFiftySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (31621 / 1000000 : Real) false false 2 2 2 2
          (749054 / 1000000) (750611 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31684 / 1000000 : Real) false false 2 2 2 2
          (750611 / 1000000) (752218 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31747 / 1000000 : Real) false false 2 2 2 2
          (752218 / 1000000) (753877 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31813 / 1000000 : Real) false false 2 2 2 2
          (753877 / 1000000) (755589 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (31881 / 1000000 : Real) false false 2 2 2 2
          (755589 / 1000000) (757356 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def fortyEighthLeaf :
    BennettGammaScaledIntervalCertificate (741971 / 1000000) (743299 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31337 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFortyEightThroughFiftyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fortyNinthLeaf :
    BennettGammaScaledIntervalCertificate (743299 / 1000000) (744670 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31390 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFortyEightThroughFiftyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fiftiethLeaf :
    BennettGammaScaledIntervalCertificate (744670 / 1000000) (746085 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31445 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFortyEightThroughFiftyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fiftyFirstLeaf :
    BennettGammaScaledIntervalCertificate (746085 / 1000000) (747546 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31503 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFortyEightThroughFiftyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fiftySecondLeaf :
    BennettGammaScaledIntervalCertificate (747546 / 1000000) (749054 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31560 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFortyEightThroughFiftyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fiftyThirdLeaf :
    BennettGammaScaledIntervalCertificate (749054 / 1000000) (750611 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31621 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFiftyThreeThroughFiftySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fiftyFourthLeaf :
    BennettGammaScaledIntervalCertificate (750611 / 1000000) (752218 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31684 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFiftyThreeThroughFiftySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fiftyFifthLeaf :
    BennettGammaScaledIntervalCertificate (752218 / 1000000) (753877 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31747 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFiftyThreeThroughFiftySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fiftySixthLeaf :
    BennettGammaScaledIntervalCertificate (753877 / 1000000) (755589 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31813 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFiftyThreeThroughFiftySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fiftySeventhLeaf :
    BennettGammaScaledIntervalCertificate (755589 / 1000000) (757356 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31881 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFiftyThreeThroughFiftySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Fifty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstFiftySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (757356 / 1000000) :=
  .split (741971 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstFortySevenFiniteCertificateLeaves
    (.split (743299 / 1000000) (by norm_num) (by norm_num) fortyEighthLeaf
      (.split (744670 / 1000000) (by norm_num) (by norm_num) fortyNinthLeaf
        (.split (746085 / 1000000) (by norm_num) (by norm_num) fiftiethLeaf
          (.split (747546 / 1000000) (by norm_num) (by norm_num) fiftyFirstLeaf
            (.split (749054 / 1000000) (by norm_num) (by norm_num) fiftySecondLeaf
              (.split (750611 / 1000000) (by norm_num) (by norm_num) fiftyThirdLeaf
                (.split (752218 / 1000000) (by norm_num) (by norm_num) fiftyFourthLeaf
                  (.split (753877 / 1000000) (by norm_num) (by norm_num) fiftyFifthLeaf
                    (.split (755589 / 1000000) (by norm_num) (by norm_num)
                      fiftySixthLeaf fiftySeventhLeaf)))))))))

private theorem leavesFiftyEightThroughSixtyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (31952 / 1000000 : Real) false false 2 2 2 2
          (757356 / 1000000) (759180 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (32024 / 1000000 : Real) false true 2 2 2 2
          (759180 / 1000000) (761063 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (32100 / 1000000 : Real) true true 2 2 2 2
          (761063 / 1000000) (763007 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (32177 / 1000000 : Real) true true 2 2 2 2
          (763007 / 1000000) (765013 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (32256 / 1000000 : Real) true true 2 2 2 2
          (765013 / 1000000) (767084 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesSixtyThreeThroughSixtySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (32338 / 1000000 : Real) true true 2 2 2 2
          (767084 / 1000000) (769222 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (32423 / 1000000 : Real) true true 2 2 2 2
          (769222 / 1000000) (771429 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (32511 / 1000000 : Real) true true 2 2 2 2
          (771429 / 1000000) (773707 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (32601 / 1000000 : Real) true true 2 2 2 2
          (773707 / 1000000) (776058 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (32694 / 1000000 : Real) true false 2 2 5 0
          (776058 / 1000000) (778485 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def fiftyEighthLeaf :
    BennettGammaScaledIntervalCertificate (757356 / 1000000) (759180 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (31952 / 1000000)
    false false 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFiftyEightThroughSixtyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def fiftyNinthLeaf :
    BennettGammaScaledIntervalCertificate (759180 / 1000000) (761063 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (32024 / 1000000)
    false true 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFiftyEightThroughSixtyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def sixtiethLeaf :
    BennettGammaScaledIntervalCertificate (761063 / 1000000) (763007 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (32100 / 1000000)
    true true 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFiftyEightThroughSixtyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def sixtyFirstLeaf :
    BennettGammaScaledIntervalCertificate (763007 / 1000000) (765013 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (32177 / 1000000)
    true true 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFiftyEightThroughSixtyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def sixtySecondLeaf :
    BennettGammaScaledIntervalCertificate (765013 / 1000000) (767084 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (32256 / 1000000)
    true true 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesFiftyEightThroughSixtyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def sixtyThirdLeaf :
    BennettGammaScaledIntervalCertificate (767084 / 1000000) (769222 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (32338 / 1000000)
    true true 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSixtyThreeThroughSixtySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def sixtyFourthLeaf :
    BennettGammaScaledIntervalCertificate (769222 / 1000000) (771429 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (32423 / 1000000)
    true true 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSixtyThreeThroughSixtySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def sixtyFifthLeaf :
    BennettGammaScaledIntervalCertificate (771429 / 1000000) (773707 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (32511 / 1000000)
    true true 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSixtyThreeThroughSixtySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def sixtySixthLeaf :
    BennettGammaScaledIntervalCertificate (773707 / 1000000) (776058 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (32601 / 1000000)
    true true 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSixtyThreeThroughSixtySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def sixtySeventhLeaf :
    BennettGammaScaledIntervalCertificate (776058 / 1000000) (778485 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (32694 / 1000000)
    true false 2 2 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSixtyThreeThroughSixtySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Sixty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstSixtySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (778485 / 1000000) :=
  .split (757356 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstFiftySevenFiniteCertificateLeaves
    (.split (759180 / 1000000) (by norm_num) (by norm_num) fiftyEighthLeaf
      (.split (761063 / 1000000) (by norm_num) (by norm_num) fiftyNinthLeaf
        (.split (763007 / 1000000) (by norm_num) (by norm_num) sixtiethLeaf
          (.split (765013 / 1000000) (by norm_num) (by norm_num) sixtyFirstLeaf
            (.split (767084 / 1000000) (by norm_num) (by norm_num) sixtySecondLeaf
              (.split (769222 / 1000000) (by norm_num) (by norm_num) sixtyThirdLeaf
                (.split (771429 / 1000000) (by norm_num) (by norm_num) sixtyFourthLeaf
                  (.split (773707 / 1000000) (by norm_num) (by norm_num) sixtyFifthLeaf
                    (.split (776058 / 1000000) (by norm_num) (by norm_num)
                      sixtySixthLeaf sixtySeventhLeaf)))))))))

private theorem leavesSixtyEightThroughSeventyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (32790 / 1000000 : Real) true false 2 2 5 0
          (778485 / 1000000) (780990 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (32889 / 1000000 : Real) true false 2 2 5 0
          (780990 / 1000000) (783575 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (32991 / 1000000 : Real) true false 2 2 5 0
          (783575 / 1000000) (786243 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (33096 / 1000000 : Real) false false 5 0 5 0
          (786243 / 1000000) (788997 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (33205 / 1000000 : Real) false false 5 0 5 0
          (788997 / 1000000) (791839 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesSeventyThreeThroughSeventySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (33317 / 1000000 : Real) false false 5 0 5 0
          (791839 / 1000000) (794772 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (33432 / 1000000 : Real) false false 5 0 5 0
          (794772 / 1000000) (797799 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (33551 / 1000000 : Real) false false 5 0 5 0
          (797799 / 1000000) (800923 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (33673 / 1000000 : Real) false false 5 0 5 0
          (800923 / 1000000) (804147 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (33800 / 1000000 : Real) false false 5 0 5 0
          (804147 / 1000000) (807474 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def sixtyEighthLeaf :
    BennettGammaScaledIntervalCertificate (778485 / 1000000) (780990 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (32790 / 1000000)
    true false 2 2 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSixtyEightThroughSeventyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def sixtyNinthLeaf :
    BennettGammaScaledIntervalCertificate (780990 / 1000000) (783575 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (32889 / 1000000)
    true false 2 2 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSixtyEightThroughSeventyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def seventiethLeaf :
    BennettGammaScaledIntervalCertificate (783575 / 1000000) (786243 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (32991 / 1000000)
    true false 2 2 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSixtyEightThroughSeventyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def seventyFirstLeaf :
    BennettGammaScaledIntervalCertificate (786243 / 1000000) (788997 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (33096 / 1000000)
    false false 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSixtyEightThroughSeventyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def seventySecondLeaf :
    BennettGammaScaledIntervalCertificate (788997 / 1000000) (791839 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (33205 / 1000000)
    false false 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSixtyEightThroughSeventyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def seventyThirdLeaf :
    BennettGammaScaledIntervalCertificate (791839 / 1000000) (794772 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (33317 / 1000000)
    false false 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSeventyThreeThroughSeventySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def seventyFourthLeaf :
    BennettGammaScaledIntervalCertificate (794772 / 1000000) (797799 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (33432 / 1000000)
    false false 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSeventyThreeThroughSeventySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def seventyFifthLeaf :
    BennettGammaScaledIntervalCertificate (797799 / 1000000) (800923 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (33551 / 1000000)
    false false 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSeventyThreeThroughSeventySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def seventySixthLeaf :
    BennettGammaScaledIntervalCertificate (800923 / 1000000) (804147 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (33673 / 1000000)
    false false 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSeventyThreeThroughSeventySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def seventySeventhLeaf :
    BennettGammaScaledIntervalCertificate (804147 / 1000000) (807474 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (33800 / 1000000)
    false false 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSeventyThreeThroughSeventySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Seventy-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstSeventySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (807474 / 1000000) :=
  .split (778485 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstSixtySevenFiniteCertificateLeaves
    (.split (780990 / 1000000) (by norm_num) (by norm_num) sixtyEighthLeaf
      (.split (783575 / 1000000) (by norm_num) (by norm_num) sixtyNinthLeaf
        (.split (786243 / 1000000) (by norm_num) (by norm_num) seventiethLeaf
          (.split (788997 / 1000000) (by norm_num) (by norm_num) seventyFirstLeaf
            (.split (791839 / 1000000) (by norm_num) (by norm_num) seventySecondLeaf
              (.split (794772 / 1000000) (by norm_num) (by norm_num) seventyThirdLeaf
                (.split (797799 / 1000000) (by norm_num) (by norm_num) seventyFourthLeaf
                  (.split (800923 / 1000000) (by norm_num) (by norm_num) seventyFifthLeaf
                    (.split (804147 / 1000000) (by norm_num) (by norm_num)
                      seventySixthLeaf seventySeventhLeaf)))))))))

private theorem leavesSeventyEightThroughEightyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (33930 / 1000000 : Real) false true 5 0 5 0
          (807474 / 1000000) (810907 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (34064 / 1000000 : Real) true true 5 0 5 0
          (810907 / 1000000) (814450 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (34202 / 1000000 : Real) true true 5 0 5 0
          (814450 / 1000000) (818106 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (34345 / 1000000 : Real) true true 5 0 5 0
          (818106 / 1000000) (821878 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (34492 / 1000000 : Real) true true 5 0 5 0
          (821878 / 1000000) (825770 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesEightyThreeThroughEightySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (34643 / 1000000 : Real) true true 5 0 5 0
          (825770 / 1000000) (829785 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (34798 / 1000000 : Real) true true 5 0 5 0
          (829785 / 1000000) (833927 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (34959 / 1000000 : Real) true false 5 0 0 3
          (833927 / 1000000) (838200 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (35124 / 1000000 : Real) true false 5 0 0 3
          (838200 / 1000000) (842607 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (35294 / 1000000 : Real) true false 5 0 0 3
          (842607 / 1000000) (847153 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def seventyEighthLeaf :
    BennettGammaScaledIntervalCertificate (807474 / 1000000) (810907 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (33930 / 1000000)
    false true 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSeventyEightThroughEightyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def seventyNinthLeaf :
    BennettGammaScaledIntervalCertificate (810907 / 1000000) (814450 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (34064 / 1000000)
    true true 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSeventyEightThroughEightyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def eightiethLeaf :
    BennettGammaScaledIntervalCertificate (814450 / 1000000) (818106 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (34202 / 1000000)
    true true 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSeventyEightThroughEightyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def eightyFirstLeaf :
    BennettGammaScaledIntervalCertificate (818106 / 1000000) (821878 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (34345 / 1000000)
    true true 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSeventyEightThroughEightyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def eightySecondLeaf :
    BennettGammaScaledIntervalCertificate (821878 / 1000000) (825770 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (34492 / 1000000)
    true true 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesSeventyEightThroughEightyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def eightyThirdLeaf :
    BennettGammaScaledIntervalCertificate (825770 / 1000000) (829785 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (34643 / 1000000)
    true true 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEightyThreeThroughEightySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def eightyFourthLeaf :
    BennettGammaScaledIntervalCertificate (829785 / 1000000) (833927 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (34798 / 1000000)
    true true 5 0 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEightyThreeThroughEightySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def eightyFifthLeaf :
    BennettGammaScaledIntervalCertificate (833927 / 1000000) (838200 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (34959 / 1000000)
    true false 5 0 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEightyThreeThroughEightySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def eightySixthLeaf :
    BennettGammaScaledIntervalCertificate (838200 / 1000000) (842607 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (35124 / 1000000)
    true false 5 0 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEightyThreeThroughEightySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def eightySeventhLeaf :
    BennettGammaScaledIntervalCertificate (842607 / 1000000) (847153 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (35294 / 1000000)
    true false 5 0 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEightyThreeThroughEightySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Eighty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstEightySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (847153 / 1000000) :=
  .split (807474 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstSeventySevenFiniteCertificateLeaves
    (.split (810907 / 1000000) (by norm_num) (by norm_num) seventyEighthLeaf
      (.split (814450 / 1000000) (by norm_num) (by norm_num) seventyNinthLeaf
        (.split (818106 / 1000000) (by norm_num) (by norm_num) eightiethLeaf
          (.split (821878 / 1000000) (by norm_num) (by norm_num) eightyFirstLeaf
            (.split (825770 / 1000000) (by norm_num) (by norm_num) eightySecondLeaf
              (.split (829785 / 1000000) (by norm_num) (by norm_num) eightyThirdLeaf
                (.split (833927 / 1000000) (by norm_num) (by norm_num) eightyFourthLeaf
                  (.split (838200 / 1000000) (by norm_num) (by norm_num) eightyFifthLeaf
                    (.split (842607 / 1000000) (by norm_num) (by norm_num)
                      eightySixthLeaf eightySeventhLeaf)))))))))

private theorem leavesEightyEightThroughNinetyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (35469 / 1000000 : Real) false false 0 3 0 3
          (847153 / 1000000) (851842 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (35650 / 1000000 : Real) false false 0 3 0 3
          (851842 / 1000000) (856677 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (35835 / 1000000 : Real) false false 0 3 0 3
          (856677 / 1000000) (861663 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (36026 / 1000000 : Real) false false 0 3 0 3
          (861663 / 1000000) (866805 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (36223 / 1000000 : Real) false false 0 3 0 3
          (866805 / 1000000) (872106 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesNinetyThreeThroughNinetySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (36425 / 1000000 : Real) false false 0 3 0 3
          (872106 / 1000000) (877571 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (36633 / 1000000 : Real) false true 0 3 0 3
          (877571 / 1000000) (883205 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (36846 / 1000000 : Real) true true 0 3 0 3
          (883205 / 1000000) (889012 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (37066 / 1000000 : Real) true true 0 3 0 3
          (889012 / 1000000) (894996 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (37292 / 1000000 : Real) true true 0 3 0 3
          (894996 / 1000000) (901163 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def eightyEighthLeaf :
    BennettGammaScaledIntervalCertificate (847153 / 1000000) (851842 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (35469 / 1000000)
    false false 0 3 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEightyEightThroughNinetyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def eightyNinthLeaf :
    BennettGammaScaledIntervalCertificate (851842 / 1000000) (856677 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (35650 / 1000000)
    false false 0 3 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEightyEightThroughNinetyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def ninetiethLeaf :
    BennettGammaScaledIntervalCertificate (856677 / 1000000) (861663 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (35835 / 1000000)
    false false 0 3 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEightyEightThroughNinetyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def ninetyFirstLeaf :
    BennettGammaScaledIntervalCertificate (861663 / 1000000) (866805 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (36026 / 1000000)
    false false 0 3 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEightyEightThroughNinetyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def ninetySecondLeaf :
    BennettGammaScaledIntervalCertificate (866805 / 1000000) (872106 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (36223 / 1000000)
    false false 0 3 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesEightyEightThroughNinetyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def ninetyThirdLeaf :
    BennettGammaScaledIntervalCertificate (872106 / 1000000) (877571 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (36425 / 1000000)
    false false 0 3 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesNinetyThreeThroughNinetySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def ninetyFourthLeaf :
    BennettGammaScaledIntervalCertificate (877571 / 1000000) (883205 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (36633 / 1000000)
    false true 0 3 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesNinetyThreeThroughNinetySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def ninetyFifthLeaf :
    BennettGammaScaledIntervalCertificate (883205 / 1000000) (889012 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (36846 / 1000000)
    true true 0 3 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesNinetyThreeThroughNinetySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def ninetySixthLeaf :
    BennettGammaScaledIntervalCertificate (889012 / 1000000) (894996 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (37066 / 1000000)
    true true 0 3 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesNinetyThreeThroughNinetySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def ninetySeventhLeaf :
    BennettGammaScaledIntervalCertificate (894996 / 1000000) (901163 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (37292 / 1000000)
    true true 0 3 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesNinetyThreeThroughNinetySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Ninety-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstNinetySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (901163 / 1000000) :=
  .split (847153 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstEightySevenFiniteCertificateLeaves
    (.split (851842 / 1000000) (by norm_num) (by norm_num) eightyEighthLeaf
      (.split (856677 / 1000000) (by norm_num) (by norm_num) eightyNinthLeaf
        (.split (861663 / 1000000) (by norm_num) (by norm_num) ninetiethLeaf
          (.split (866805 / 1000000) (by norm_num) (by norm_num) ninetyFirstLeaf
            (.split (872106 / 1000000) (by norm_num) (by norm_num) ninetySecondLeaf
              (.split (877571 / 1000000) (by norm_num) (by norm_num) ninetyThirdLeaf
                (.split (883205 / 1000000) (by norm_num) (by norm_num) ninetyFourthLeaf
                  (.split (889012 / 1000000) (by norm_num) (by norm_num) ninetyFifthLeaf
                    (.split (894996 / 1000000) (by norm_num) (by norm_num)
                      ninetySixthLeaf ninetySeventhLeaf)))))))))

private theorem leavesNinetyEightThroughOneHundredTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (37524 / 1000000 : Real) true false 0 3 3 1
          (901163 / 1000000) (907517 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (37763 / 1000000 : Real) true false 0 3 3 1
          (907517 / 1000000) (914063 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (38008 / 1000000 : Real) false false 3 1 3 1
          (914063 / 1000000) (920805 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (38260 / 1000000 : Real) false false 3 1 3 1
          (920805 / 1000000) (927749 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (38518 / 1000000 : Real) false false 3 1 3 1
          (927749 / 1000000) (934900 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesOneHundredThreeThroughOneHundredSevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (38783 / 1000000 : Real) false true 3 1 3 1
          (934900 / 1000000) (942262 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (39056 / 1000000 : Real) true true 3 1 3 1
          (942262 / 1000000) (949840 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (39335 / 1000000 : Real) true true 3 1 3 1
          (949840 / 1000000) (957640 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (39621 / 1000000 : Real) true true 3 1 3 1
          (957640 / 1000000) (965666 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (39915 / 1000000 : Real) true true 3 1 3 1
          (965666 / 1000000) (973923 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def ninetyEighthLeaf :
    BennettGammaScaledIntervalCertificate (901163 / 1000000) (907517 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (37524 / 1000000)
    true false 0 3 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesNinetyEightThroughOneHundredTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def ninetyNinthLeaf :
    BennettGammaScaledIntervalCertificate (907517 / 1000000) (914063 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (37763 / 1000000)
    true false 0 3 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesNinetyEightThroughOneHundredTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredthLeaf :
    BennettGammaScaledIntervalCertificate (914063 / 1000000) (920805 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (38008 / 1000000)
    false false 3 1 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesNinetyEightThroughOneHundredTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFirstLeaf :
    BennettGammaScaledIntervalCertificate (920805 / 1000000) (927749 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (38260 / 1000000)
    false false 3 1 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesNinetyEightThroughOneHundredTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSecondLeaf :
    BennettGammaScaledIntervalCertificate (927749 / 1000000) (934900 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (38518 / 1000000)
    false false 3 1 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesNinetyEightThroughOneHundredTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredThirdLeaf :
    BennettGammaScaledIntervalCertificate (934900 / 1000000) (942262 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (38783 / 1000000)
    false true 3 1 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThreeThroughOneHundredSevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFourthLeaf :
    BennettGammaScaledIntervalCertificate (942262 / 1000000) (949840 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (39056 / 1000000)
    true true 3 1 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThreeThroughOneHundredSevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFifthLeaf :
    BennettGammaScaledIntervalCertificate (949840 / 1000000) (957640 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (39335 / 1000000)
    true true 3 1 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThreeThroughOneHundredSevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSixthLeaf :
    BennettGammaScaledIntervalCertificate (957640 / 1000000) (965666 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (39621 / 1000000)
    true true 3 1 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThreeThroughOneHundredSevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSeventhLeaf :
    BennettGammaScaledIntervalCertificate (965666 / 1000000) (973923 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (39915 / 1000000)
    true true 3 1 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThreeThroughOneHundredSevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- One hundred seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstOneHundredSevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (973923 / 1000000) :=
  .split (901163 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstNinetySevenFiniteCertificateLeaves
    (.split (907517 / 1000000) (by norm_num) (by norm_num) ninetyEighthLeaf
      (.split (914063 / 1000000) (by norm_num) (by norm_num) ninetyNinthLeaf
        (.split (920805 / 1000000) (by norm_num) (by norm_num) oneHundredthLeaf
          (.split (927749 / 1000000) (by norm_num) (by norm_num) oneHundredFirstLeaf
            (.split (934900 / 1000000) (by norm_num) (by norm_num) oneHundredSecondLeaf
              (.split (942262 / 1000000) (by norm_num) (by norm_num) oneHundredThirdLeaf
                (.split (949840 / 1000000) (by norm_num) (by norm_num) oneHundredFourthLeaf
                  (.split (957640 / 1000000) (by norm_num) (by norm_num) oneHundredFifthLeaf
                    (.split (965666 / 1000000) (by norm_num) (by norm_num)
                      oneHundredSixthLeaf oneHundredSeventhLeaf)))))))))

private theorem leavesOneHundredEightThroughOneHundredTwelveRationalValid :
    BennettGammaRationalIntervalBoxValid
        (40215 / 1000000 : Real) true true 3 1 3 1
          (973923 / 1000000) (982417 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (40524 / 1000000 : Real) true true 3 1 3 1
          (982417 / 1000000) (991151 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (40839 / 1000000 : Real) true false 3 1 1 2
          (991151 / 1000000) (1000115 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (41161 / 1000000 : Real) true false 3 1 1 2
          (1000115 / 1000000) (1009332 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (41491 / 1000000 : Real) true false 3 1 1 2
          (1009332 / 1000000) (1018806 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesOneHundredThirteenThroughOneHundredSeventeenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (41829 / 1000000 : Real) false false 1 2 1 2
          (1018806 / 1000000) (1028542 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (42174 / 1000000 : Real) false false 1 2 1 2
          (1028542 / 1000000) (1038544 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (42527 / 1000000 : Real) false false 1 2 1 2
          (1038544 / 1000000) (1048817 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (42888 / 1000000 : Real) false false 1 2 1 2
          (1048817 / 1000000) (1059365 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (43256 / 1000000 : Real) false false 1 2 1 2
          (1059365 / 1000000) (1070192 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def oneHundredEighthLeaf :
    BennettGammaScaledIntervalCertificate (973923 / 1000000) (982417 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (40215 / 1000000)
    true true 3 1 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightThroughOneHundredTwelveRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredNinthLeaf :
    BennettGammaScaledIntervalCertificate (982417 / 1000000) (991151 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (40524 / 1000000)
    true true 3 1 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightThroughOneHundredTwelveRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredTenthLeaf :
    BennettGammaScaledIntervalCertificate (991151 / 1000000) (1000115 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (40839 / 1000000)
    true false 3 1 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightThroughOneHundredTwelveRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredEleventhLeaf :
    BennettGammaScaledIntervalCertificate (1000115 / 1000000) (1009332 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (41161 / 1000000)
    true false 3 1 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightThroughOneHundredTwelveRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredTwelfthLeaf :
    BennettGammaScaledIntervalCertificate (1009332 / 1000000) (1018806 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (41491 / 1000000)
    true false 3 1 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightThroughOneHundredTwelveRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredThirteenthLeaf :
    BennettGammaScaledIntervalCertificate (1018806 / 1000000) (1028542 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (41829 / 1000000)
    false false 1 2 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirteenThroughOneHundredSeventeenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFourteenthLeaf :
    BennettGammaScaledIntervalCertificate (1028542 / 1000000) (1038544 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (42174 / 1000000)
    false false 1 2 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirteenThroughOneHundredSeventeenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFifteenthLeaf :
    BennettGammaScaledIntervalCertificate (1038544 / 1000000) (1048817 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (42527 / 1000000)
    false false 1 2 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirteenThroughOneHundredSeventeenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSixteenthLeaf :
    BennettGammaScaledIntervalCertificate (1048817 / 1000000) (1059365 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (42888 / 1000000)
    false false 1 2 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirteenThroughOneHundredSeventeenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSeventeenthLeaf :
    BennettGammaScaledIntervalCertificate (1059365 / 1000000) (1070192 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (43256 / 1000000)
    false false 1 2 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirteenThroughOneHundredSeventeenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- One hundred seventeen checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstOneHundredSeventeenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (1070192 / 1000000) :=
  .split (973923 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstOneHundredSevenFiniteCertificateLeaves
    (.split (982417 / 1000000) (by norm_num) (by norm_num) oneHundredEighthLeaf
      (.split (991151 / 1000000) (by norm_num) (by norm_num) oneHundredNinthLeaf
        (.split (1000115 / 1000000) (by norm_num) (by norm_num) oneHundredTenthLeaf
          (.split (1009332 / 1000000) (by norm_num) (by norm_num) oneHundredEleventhLeaf
            (.split (1018806 / 1000000) (by norm_num) (by norm_num) oneHundredTwelfthLeaf
              (.split (1028542 / 1000000) (by norm_num) (by norm_num) oneHundredThirteenthLeaf
                (.split (1038544 / 1000000) (by norm_num) (by norm_num) oneHundredFourteenthLeaf
                  (.split (1048817 / 1000000) (by norm_num) (by norm_num) oneHundredFifteenthLeaf
                    (.split (1059365 / 1000000) (by norm_num) (by norm_num)
                      oneHundredSixteenthLeaf oneHundredSeventeenthLeaf)))))))))

private theorem leavesOneHundredEighteenThroughOneHundredTwentyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (43632 / 1000000 : Real) false false 1 2 1 2
          (1070192 / 1000000) (1081302 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (44016 / 1000000 : Real) false true 1 2 1 2
          (1081302 / 1000000) (1092700 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (44407 / 1000000 : Real) true true 1 2 1 2
          (1092700 / 1000000) (1104389 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (44805 / 1000000 : Real) true true 1 2 1 2
          (1104389 / 1000000) (1116372 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (45211 / 1000000 : Real) true false 1 2 4 0
          (1116372 / 1000000) (1128654 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesOneHundredTwentyThreeThroughOneHundredTwentySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (45624 / 1000000 : Real) false false 4 0 4 0
          (1128654 / 1000000) (1141237 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (46045 / 1000000 : Real) false false 4 0 4 0
          (1141237 / 1000000) (1154124 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (46472 / 1000000 : Real) false true 4 0 4 0
          (1154124 / 1000000) (1167318 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (46906 / 1000000 : Real) true true 4 0 4 0
          (1167318 / 1000000) (1180821 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (47347 / 1000000 : Real) true true 4 0 4 0
          (1180821 / 1000000) (1194636 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def oneHundredEighteenthLeaf :
    BennettGammaScaledIntervalCertificate (1070192 / 1000000) (1081302 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (43632 / 1000000)
    false false 1 2 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEighteenThroughOneHundredTwentyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredNineteenthLeaf :
    BennettGammaScaledIntervalCertificate (1081302 / 1000000) (1092700 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (44016 / 1000000)
    false true 1 2 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEighteenThroughOneHundredTwentyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredTwentiethLeaf :
    BennettGammaScaledIntervalCertificate (1092700 / 1000000) (1104389 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (44407 / 1000000)
    true true 1 2 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEighteenThroughOneHundredTwentyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredTwentyFirstLeaf :
    BennettGammaScaledIntervalCertificate (1104389 / 1000000) (1116372 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (44805 / 1000000)
    true true 1 2 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEighteenThroughOneHundredTwentyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredTwentySecondLeaf :
    BennettGammaScaledIntervalCertificate (1116372 / 1000000) (1128654 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (45211 / 1000000)
    true false 1 2 4 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEighteenThroughOneHundredTwentyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredTwentyThirdLeaf :
    BennettGammaScaledIntervalCertificate (1128654 / 1000000) (1141237 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (45624 / 1000000)
    false false 4 0 4 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredTwentyThreeThroughOneHundredTwentySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredTwentyFourthLeaf :
    BennettGammaScaledIntervalCertificate (1141237 / 1000000) (1154124 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (46045 / 1000000)
    false false 4 0 4 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredTwentyThreeThroughOneHundredTwentySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredTwentyFifthLeaf :
    BennettGammaScaledIntervalCertificate (1154124 / 1000000) (1167318 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (46472 / 1000000)
    false true 4 0 4 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredTwentyThreeThroughOneHundredTwentySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredTwentySixthLeaf :
    BennettGammaScaledIntervalCertificate (1167318 / 1000000) (1180821 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (46906 / 1000000)
    true true 4 0 4 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredTwentyThreeThroughOneHundredTwentySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredTwentySeventhLeaf :
    BennettGammaScaledIntervalCertificate (1180821 / 1000000) (1194636 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (47347 / 1000000)
    true true 4 0 4 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredTwentyThreeThroughOneHundredTwentySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- One hundred twenty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstOneHundredTwentySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (1194636 / 1000000) :=
  .split (1070192 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstOneHundredSeventeenFiniteCertificateLeaves
    (.split (1081302 / 1000000) (by norm_num) (by norm_num) oneHundredEighteenthLeaf
      (.split (1092700 / 1000000) (by norm_num) (by norm_num) oneHundredNineteenthLeaf
        (.split (1104389 / 1000000) (by norm_num) (by norm_num) oneHundredTwentiethLeaf
          (.split (1116372 / 1000000) (by norm_num) (by norm_num) oneHundredTwentyFirstLeaf
            (.split (1128654 / 1000000) (by norm_num) (by norm_num) oneHundredTwentySecondLeaf
              (.split (1141237 / 1000000) (by norm_num) (by norm_num) oneHundredTwentyThirdLeaf
                (.split (1154124 / 1000000) (by norm_num) (by norm_num) oneHundredTwentyFourthLeaf
                  (.split (1167318 / 1000000) (by norm_num) (by norm_num) oneHundredTwentyFifthLeaf
                    (.split (1180821 / 1000000) (by norm_num) (by norm_num)
                      oneHundredTwentySixthLeaf oneHundredTwentySeventhLeaf)))))))))

private theorem leavesOneHundredTwentyEightThroughOneHundredThirtyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (47795 / 1000000 : Real) true true 4 0 4 0
          (1194636 / 1000000) (1208764 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (48249 / 1000000 : Real) true true 4 0 4 0
          (1208764 / 1000000) (1223206 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (48709 / 1000000 : Real) true false 4 0 2 1
          (1223206 / 1000000) (1237963 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (49179 / 1000000 : Real) true false 4 0 2 1
          (1237963 / 1000000) (1253164 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (49655 / 1000000 : Real) true false 4 0 2 1
          (1253164 / 1000000) (1268701 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesOneHundredThirtyThreeThroughOneHundredThirtySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (50137 / 1000000 : Real) false false 2 1 2 1
          (1268701 / 1000000) (1284577 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (50624 / 1000000 : Real) false false 2 1 2 1
          (1284577 / 1000000) (1300793 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (51117 / 1000000 : Real) false false 2 1 2 1
          (1300793 / 1000000) (1317352 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (51615 / 1000000 : Real) false false 2 1 2 1
          (1317352 / 1000000) (1334255 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (52118 / 1000000 : Real) false false 2 1 2 1
          (1334255 / 1000000) (1351504 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def oneHundredTwentyEighthLeaf :
    BennettGammaScaledIntervalCertificate (1194636 / 1000000) (1208764 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (47795 / 1000000)
    true true 4 0 4 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredTwentyEightThroughOneHundredThirtyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredTwentyNinthLeaf :
    BennettGammaScaledIntervalCertificate (1208764 / 1000000) (1223206 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (48249 / 1000000)
    true true 4 0 4 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredTwentyEightThroughOneHundredThirtyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredThirtiethLeaf :
    BennettGammaScaledIntervalCertificate (1223206 / 1000000) (1237963 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (48709 / 1000000)
    true false 4 0 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredTwentyEightThroughOneHundredThirtyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredThirtyFirstLeaf :
    BennettGammaScaledIntervalCertificate (1237963 / 1000000) (1253164 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (49179 / 1000000)
    true false 4 0 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredTwentyEightThroughOneHundredThirtyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredThirtySecondLeaf :
    BennettGammaScaledIntervalCertificate (1253164 / 1000000) (1268701 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (49655 / 1000000)
    true false 4 0 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredTwentyEightThroughOneHundredThirtyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredThirtyThirdLeaf :
    BennettGammaScaledIntervalCertificate (1268701 / 1000000) (1284577 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (50137 / 1000000)
    false false 2 1 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirtyThreeThroughOneHundredThirtySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredThirtyFourthLeaf :
    BennettGammaScaledIntervalCertificate (1284577 / 1000000) (1300793 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (50624 / 1000000)
    false false 2 1 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirtyThreeThroughOneHundredThirtySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredThirtyFifthLeaf :
    BennettGammaScaledIntervalCertificate (1300793 / 1000000) (1317352 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (51117 / 1000000)
    false false 2 1 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirtyThreeThroughOneHundredThirtySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredThirtySixthLeaf :
    BennettGammaScaledIntervalCertificate (1317352 / 1000000) (1334255 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (51615 / 1000000)
    false false 2 1 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirtyThreeThroughOneHundredThirtySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredThirtySeventhLeaf :
    BennettGammaScaledIntervalCertificate (1334255 / 1000000) (1351504 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (52118 / 1000000)
    false false 2 1 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirtyThreeThroughOneHundredThirtySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- One hundred thirty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstOneHundredThirtySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (1351504 / 1000000) :=
  .split (1194636 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstOneHundredTwentySevenFiniteCertificateLeaves
    (.split (1208764 / 1000000) (by norm_num) (by norm_num) oneHundredTwentyEighthLeaf
      (.split (1223206 / 1000000) (by norm_num) (by norm_num) oneHundredTwentyNinthLeaf
        (.split (1237963 / 1000000) (by norm_num) (by norm_num) oneHundredThirtiethLeaf
          (.split (1253164 / 1000000) (by norm_num) (by norm_num) oneHundredThirtyFirstLeaf
            (.split (1268701 / 1000000) (by norm_num) (by norm_num) oneHundredThirtySecondLeaf
              (.split (1284577 / 1000000) (by norm_num) (by norm_num) oneHundredThirtyThirdLeaf
                (.split (1300793 / 1000000) (by norm_num) (by norm_num) oneHundredThirtyFourthLeaf
                  (.split (1317352 / 1000000) (by norm_num) (by norm_num) oneHundredThirtyFifthLeaf
                    (.split (1334255 / 1000000) (by norm_num) (by norm_num)
                      oneHundredThirtySixthLeaf oneHundredThirtySeventhLeaf)))))))))

private theorem leavesOneHundredThirtyEightThroughOneHundredFortyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (52625 / 1000000 : Real) false true 2 1 2 1
          (1351504 / 1000000) (1369101 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (53136 / 1000000 : Real) true true 2 1 2 1
          (1369101 / 1000000) (1387048 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (53652 / 1000000 : Real) true true 2 1 2 1
          (1387048 / 1000000) (1405346 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (54171 / 1000000 : Real) true true 2 1 2 1
          (1405346 / 1000000) (1423996 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (54693 / 1000000 : Real) true true 2 1 2 1
          (1423996 / 1000000) (1442998 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesOneHundredFortyThreeThroughOneHundredFortySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (55218 / 1000000 : Real) true false 2 1 0 2
          (1442998 / 1000000) (1462355 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (55745 / 1000000 : Real) true false 2 1 0 2
          (1462355 / 1000000) (1482069 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (56275 / 1000000 : Real) false false 0 2 0 2
          (1482069 / 1000000) (1502140 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (56806 / 1000000 : Real) false false 0 2 0 2
          (1502140 / 1000000) (1522569 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (57339 / 1000000 : Real) false false 0 2 0 2
          (1522569 / 1000000) (1543357 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def oneHundredThirtyEighthLeaf :
    BennettGammaScaledIntervalCertificate (1351504 / 1000000) (1369101 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (52625 / 1000000)
    false true 2 1 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirtyEightThroughOneHundredFortyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredThirtyNinthLeaf :
    BennettGammaScaledIntervalCertificate (1369101 / 1000000) (1387048 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (53136 / 1000000)
    true true 2 1 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirtyEightThroughOneHundredFortyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFortiethLeaf :
    BennettGammaScaledIntervalCertificate (1387048 / 1000000) (1405346 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (53652 / 1000000)
    true true 2 1 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirtyEightThroughOneHundredFortyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFortyFirstLeaf :
    BennettGammaScaledIntervalCertificate (1405346 / 1000000) (1423996 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (54171 / 1000000)
    true true 2 1 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirtyEightThroughOneHundredFortyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFortySecondLeaf :
    BennettGammaScaledIntervalCertificate (1423996 / 1000000) (1442998 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (54693 / 1000000)
    true true 2 1 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredThirtyEightThroughOneHundredFortyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFortyThirdLeaf :
    BennettGammaScaledIntervalCertificate (1442998 / 1000000) (1462355 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (55218 / 1000000)
    true false 2 1 0 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFortyThreeThroughOneHundredFortySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFortyFourthLeaf :
    BennettGammaScaledIntervalCertificate (1462355 / 1000000) (1482069 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (55745 / 1000000)
    true false 2 1 0 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFortyThreeThroughOneHundredFortySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFortyFifthLeaf :
    BennettGammaScaledIntervalCertificate (1482069 / 1000000) (1502140 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (56275 / 1000000)
    false false 0 2 0 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFortyThreeThroughOneHundredFortySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFortySixthLeaf :
    BennettGammaScaledIntervalCertificate (1502140 / 1000000) (1522569 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (56806 / 1000000)
    false false 0 2 0 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFortyThreeThroughOneHundredFortySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFortySeventhLeaf :
    BennettGammaScaledIntervalCertificate (1522569 / 1000000) (1543357 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (57339 / 1000000)
    false false 0 2 0 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFortyThreeThroughOneHundredFortySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- One hundred forty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstOneHundredFortySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (1543357 / 1000000) :=
  .split (1351504 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstOneHundredThirtySevenFiniteCertificateLeaves
    (.split (1369101 / 1000000) (by norm_num) (by norm_num) oneHundredThirtyEighthLeaf
      (.split (1387048 / 1000000) (by norm_num) (by norm_num) oneHundredThirtyNinthLeaf
        (.split (1405346 / 1000000) (by norm_num) (by norm_num) oneHundredFortiethLeaf
          (.split (1423996 / 1000000) (by norm_num) (by norm_num) oneHundredFortyFirstLeaf
            (.split (1442998 / 1000000) (by norm_num) (by norm_num) oneHundredFortySecondLeaf
              (.split (1462355 / 1000000) (by norm_num) (by norm_num) oneHundredFortyThirdLeaf
                (.split (1482069 / 1000000) (by norm_num) (by norm_num) oneHundredFortyFourthLeaf
                  (.split (1502140 / 1000000) (by norm_num) (by norm_num) oneHundredFortyFifthLeaf
                    (.split (1522569 / 1000000) (by norm_num) (by norm_num)
                      oneHundredFortySixthLeaf oneHundredFortySeventhLeaf)))))))))

private theorem leavesOneHundredFortyEightThroughOneHundredFiftyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (57872 / 1000000 : Real) false false 0 2 0 2
          (1543357 / 1000000) (1564505 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (58406 / 1000000 : Real) false false 0 2 0 2
          (1564505 / 1000000) (1586014 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (58940 / 1000000 : Real) false true 0 2 0 2
          (1586014 / 1000000) (1607886 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (59473 / 1000000 : Real) true true 0 2 0 2
          (1607886 / 1000000) (1630121 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (60006 / 1000000 : Real) true false 0 2 3 0
          (1630121 / 1000000) (1652721 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesOneHundredFiftyThreeThroughOneHundredFiftySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (60538 / 1000000 : Real) false false 3 0 3 0
          (1652721 / 1000000) (1675687 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (61068 / 1000000 : Real) false false 3 0 3 0
          (1675687 / 1000000) (1699021 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (61595 / 1000000 : Real) false true 3 0 3 0
          (1699021 / 1000000) (1722724 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (62121 / 1000000 : Real) true true 3 0 3 0
          (1722724 / 1000000) (1746798 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (62644 / 1000000 : Real) true true 3 0 3 0
          (1746798 / 1000000) (1771244 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def oneHundredFortyEighthLeaf :
    BennettGammaScaledIntervalCertificate (1543357 / 1000000) (1564505 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (57872 / 1000000)
    false false 0 2 0 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFortyEightThroughOneHundredFiftyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFortyNinthLeaf :
    BennettGammaScaledIntervalCertificate (1564505 / 1000000) (1586014 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (58406 / 1000000)
    false false 0 2 0 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFortyEightThroughOneHundredFiftyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFiftiethLeaf :
    BennettGammaScaledIntervalCertificate (1586014 / 1000000) (1607886 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (58940 / 1000000)
    false true 0 2 0 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFortyEightThroughOneHundredFiftyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFiftyFirstLeaf :
    BennettGammaScaledIntervalCertificate (1607886 / 1000000) (1630121 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (59473 / 1000000)
    true true 0 2 0 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFortyEightThroughOneHundredFiftyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFiftySecondLeaf :
    BennettGammaScaledIntervalCertificate (1630121 / 1000000) (1652721 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (60006 / 1000000)
    true false 0 2 3 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFortyEightThroughOneHundredFiftyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFiftyThirdLeaf :
    BennettGammaScaledIntervalCertificate (1652721 / 1000000) (1675687 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (60538 / 1000000)
    false false 3 0 3 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFiftyThreeThroughOneHundredFiftySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFiftyFourthLeaf :
    BennettGammaScaledIntervalCertificate (1675687 / 1000000) (1699021 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (61068 / 1000000)
    false false 3 0 3 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFiftyThreeThroughOneHundredFiftySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFiftyFifthLeaf :
    BennettGammaScaledIntervalCertificate (1699021 / 1000000) (1722724 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (61595 / 1000000)
    false true 3 0 3 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFiftyThreeThroughOneHundredFiftySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFiftySixthLeaf :
    BennettGammaScaledIntervalCertificate (1722724 / 1000000) (1746798 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (62121 / 1000000)
    true true 3 0 3 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFiftyThreeThroughOneHundredFiftySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFiftySeventhLeaf :
    BennettGammaScaledIntervalCertificate (1746798 / 1000000) (1771244 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (62644 / 1000000)
    true true 3 0 3 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFiftyThreeThroughOneHundredFiftySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- One hundred fifty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstOneHundredFiftySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (1771244 / 1000000) :=
  .split (1543357 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstOneHundredFortySevenFiniteCertificateLeaves
    (.split (1564505 / 1000000) (by norm_num) (by norm_num) oneHundredFortyEighthLeaf
      (.split (1586014 / 1000000) (by norm_num) (by norm_num) oneHundredFortyNinthLeaf
        (.split (1607886 / 1000000) (by norm_num) (by norm_num) oneHundredFiftiethLeaf
          (.split (1630121 / 1000000) (by norm_num) (by norm_num) oneHundredFiftyFirstLeaf
            (.split (1652721 / 1000000) (by norm_num) (by norm_num) oneHundredFiftySecondLeaf
              (.split (1675687 / 1000000) (by norm_num) (by norm_num) oneHundredFiftyThirdLeaf
                (.split (1699021 / 1000000) (by norm_num) (by norm_num) oneHundredFiftyFourthLeaf
                  (.split (1722724 / 1000000) (by norm_num) (by norm_num) oneHundredFiftyFifthLeaf
                    (.split (1746798 / 1000000) (by norm_num) (by norm_num)
                      oneHundredFiftySixthLeaf oneHundredFiftySeventhLeaf)))))))))

private theorem leavesOneHundredFiftyEightThroughOneHundredSixtyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (63162 / 1000000 : Real) true true 3 0 3 0
          (1771244 / 1000000) (1796064 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (63676 / 1000000 : Real) true false 3 0 1 1
          (1796064 / 1000000) (1821259 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (64187 / 1000000 : Real) true false 3 0 1 1
          (1821259 / 1000000) (1846835 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (64693 / 1000000 : Real) true false 3 0 1 1
          (1846835 / 1000000) (1872793 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (65193 / 1000000 : Real) false false 1 1 1 1
          (1872793 / 1000000) (1899136 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesOneHundredSixtyThreeThroughOneHundredSixtySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (65688 / 1000000 : Real) false false 1 1 1 1
          (1899136 / 1000000) (1925866 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (66177 / 1000000 : Real) false false 1 1 1 1
          (1925866 / 1000000) (1952987 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (66659 / 1000000 : Real) false false 1 1 1 1
          (1952987 / 1000000) (1980502 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (67134 / 1000000 : Real) false false 1 1 1 1
          (1980502 / 1000000) (2008415 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (67602 / 1000000 : Real) false true 1 1 1 1
          (2008415 / 1000000) (2036729 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def oneHundredFiftyEighthLeaf :
    BennettGammaScaledIntervalCertificate (1771244 / 1000000) (1796064 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (63162 / 1000000)
    true true 3 0 3 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFiftyEightThroughOneHundredSixtyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredFiftyNinthLeaf :
    BennettGammaScaledIntervalCertificate (1796064 / 1000000) (1821259 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (63676 / 1000000)
    true false 3 0 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFiftyEightThroughOneHundredSixtyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSixtiethLeaf :
    BennettGammaScaledIntervalCertificate (1821259 / 1000000) (1846835 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (64187 / 1000000)
    true false 3 0 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFiftyEightThroughOneHundredSixtyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSixtyFirstLeaf :
    BennettGammaScaledIntervalCertificate (1846835 / 1000000) (1872793 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (64693 / 1000000)
    true false 3 0 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFiftyEightThroughOneHundredSixtyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSixtySecondLeaf :
    BennettGammaScaledIntervalCertificate (1872793 / 1000000) (1899136 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (65193 / 1000000)
    false false 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredFiftyEightThroughOneHundredSixtyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSixtyThirdLeaf :
    BennettGammaScaledIntervalCertificate (1899136 / 1000000) (1925866 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (65688 / 1000000)
    false false 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSixtyThreeThroughOneHundredSixtySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSixtyFourthLeaf :
    BennettGammaScaledIntervalCertificate (1925866 / 1000000) (1952987 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (66177 / 1000000)
    false false 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSixtyThreeThroughOneHundredSixtySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSixtyFifthLeaf :
    BennettGammaScaledIntervalCertificate (1952987 / 1000000) (1980502 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (66659 / 1000000)
    false false 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSixtyThreeThroughOneHundredSixtySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSixtySixthLeaf :
    BennettGammaScaledIntervalCertificate (1980502 / 1000000) (2008415 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (67134 / 1000000)
    false false 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSixtyThreeThroughOneHundredSixtySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSixtySeventhLeaf :
    BennettGammaScaledIntervalCertificate (2008415 / 1000000) (2036729 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (67602 / 1000000)
    false true 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSixtyThreeThroughOneHundredSixtySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- One hundred sixty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstOneHundredSixtySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (2036729 / 1000000) :=
  .split (1771244 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstOneHundredFiftySevenFiniteCertificateLeaves
    (.split (1796064 / 1000000) (by norm_num) (by norm_num) oneHundredFiftyEighthLeaf
      (.split (1821259 / 1000000) (by norm_num) (by norm_num) oneHundredFiftyNinthLeaf
        (.split (1846835 / 1000000) (by norm_num) (by norm_num) oneHundredSixtiethLeaf
          (.split (1872793 / 1000000) (by norm_num) (by norm_num) oneHundredSixtyFirstLeaf
            (.split (1899136 / 1000000) (by norm_num) (by norm_num) oneHundredSixtySecondLeaf
              (.split (1925866 / 1000000) (by norm_num) (by norm_num) oneHundredSixtyThirdLeaf
                (.split (1952987 / 1000000) (by norm_num) (by norm_num) oneHundredSixtyFourthLeaf
                  (.split (1980502 / 1000000) (by norm_num) (by norm_num) oneHundredSixtyFifthLeaf
                    (.split (2008415 / 1000000) (by norm_num) (by norm_num)
                      oneHundredSixtySixthLeaf oneHundredSixtySeventhLeaf)))))))))

private theorem leavesOneHundredSixtyEightThroughOneHundredSeventyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (68061 / 1000000 : Real) true true 1 1 1 1
          (2036729 / 1000000) (2065449 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (68513 / 1000000 : Real) true true 1 1 1 1
          (2065449 / 1000000) (2094578 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (68955 / 1000000 : Real) true true 1 1 1 1
          (2094578 / 1000000) (2124120 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (69388 / 1000000 : Real) true true 1 1 1 1
          (2124120 / 1000000) (2154079 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (69812 / 1000000 : Real) true true 1 1 1 1
          (2154079 / 1000000) (2184455 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesOneHundredSeventyThreeThroughOneHundredSeventySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (70224 / 1000000 : Real) true true 1 1 1 1
          (2184455 / 1000000) (2215245 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (70627 / 1000000 : Real) true false 1 1 2 0
          (2215245 / 1000000) (2246456 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (71018 / 1000000 : Real) true false 1 1 2 0
          (2246456 / 1000000) (2278122 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (71399 / 1000000 : Real) true false 1 1 2 0
          (2278122 / 1000000) (2310361 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (71769 / 1000000 : Real) false false 2 0 2 0
          (2310361 / 1000000) (2343082 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def oneHundredSixtyEighthLeaf :
    BennettGammaScaledIntervalCertificate (2036729 / 1000000) (2065449 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (68061 / 1000000)
    true true 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSixtyEightThroughOneHundredSeventyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSixtyNinthLeaf :
    BennettGammaScaledIntervalCertificate (2065449 / 1000000) (2094578 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (68513 / 1000000)
    true true 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSixtyEightThroughOneHundredSeventyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSeventiethLeaf :
    BennettGammaScaledIntervalCertificate (2094578 / 1000000) (2124120 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (68955 / 1000000)
    true true 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSixtyEightThroughOneHundredSeventyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSeventyFirstLeaf :
    BennettGammaScaledIntervalCertificate (2124120 / 1000000) (2154079 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (69388 / 1000000)
    true true 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSixtyEightThroughOneHundredSeventyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSeventySecondLeaf :
    BennettGammaScaledIntervalCertificate (2154079 / 1000000) (2184455 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (69812 / 1000000)
    true true 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSixtyEightThroughOneHundredSeventyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSeventyThirdLeaf :
    BennettGammaScaledIntervalCertificate (2184455 / 1000000) (2215245 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (70224 / 1000000)
    true true 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSeventyThreeThroughOneHundredSeventySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSeventyFourthLeaf :
    BennettGammaScaledIntervalCertificate (2215245 / 1000000) (2246456 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (70627 / 1000000)
    true false 1 1 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSeventyThreeThroughOneHundredSeventySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSeventyFifthLeaf :
    BennettGammaScaledIntervalCertificate (2246456 / 1000000) (2278122 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (71018 / 1000000)
    true false 1 1 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSeventyThreeThroughOneHundredSeventySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSeventySixthLeaf :
    BennettGammaScaledIntervalCertificate (2278122 / 1000000) (2310361 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (71399 / 1000000)
    true false 1 1 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSeventyThreeThroughOneHundredSeventySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSeventySeventhLeaf :
    BennettGammaScaledIntervalCertificate (2310361 / 1000000) (2343082 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (71769 / 1000000)
    false false 2 0 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSeventyThreeThroughOneHundredSeventySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- One hundred seventy-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstOneHundredSeventySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (2343082 / 1000000) :=
  .split (2036729 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstOneHundredSixtySevenFiniteCertificateLeaves
    (.split (2065449 / 1000000) (by norm_num) (by norm_num) oneHundredSixtyEighthLeaf
      (.split (2094578 / 1000000) (by norm_num) (by norm_num) oneHundredSixtyNinthLeaf
        (.split (2124120 / 1000000) (by norm_num) (by norm_num) oneHundredSeventiethLeaf
          (.split (2154079 / 1000000) (by norm_num) (by norm_num) oneHundredSeventyFirstLeaf
            (.split (2184455 / 1000000) (by norm_num) (by norm_num) oneHundredSeventySecondLeaf
              (.split (2215245 / 1000000) (by norm_num) (by norm_num) oneHundredSeventyThirdLeaf
                (.split (2246456 / 1000000) (by norm_num) (by norm_num) oneHundredSeventyFourthLeaf
                  (.split (2278122 / 1000000) (by norm_num) (by norm_num) oneHundredSeventyFifthLeaf
                    (.split (2310361 / 1000000) (by norm_num) (by norm_num)
                      oneHundredSeventySixthLeaf oneHundredSeventySeventhLeaf)))))))))

private theorem leavesOneHundredSeventyEightThroughOneHundredEightyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (72126 / 1000000 : Real) false false 2 0 2 0
          (2343082 / 1000000) (2376293 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (72471 / 1000000 : Real) false false 2 0 2 0
          (2376293 / 1000000) (2410001 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (72803 / 1000000 : Real) false false 2 0 2 0
          (2410001 / 1000000) (2444217 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (73121 / 1000000 : Real) false false 2 0 2 0
          (2444217 / 1000000) (2478952 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (73425 / 1000000 : Real) false false 2 0 2 0
          (2478952 / 1000000) (2514218 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesOneHundredEightyThreeThroughOneHundredEightySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (73715 / 1000000 : Real) false false 2 0 2 0
          (2514218 / 1000000) (2550028 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (73990 / 1000000 : Real) false false 2 0 2 0
          (2550028 / 1000000) (2586395 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (74250 / 1000000 : Real) false true 2 0 2 0
          (2586395 / 1000000) (2623333 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (74494 / 1000000 : Real) true true 2 0 2 0
          (2623333 / 1000000) (2660858 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (74722 / 1000000 : Real) true true 2 0 2 0
          (2660858 / 1000000) (2698985 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def oneHundredSeventyEighthLeaf :
    BennettGammaScaledIntervalCertificate (2343082 / 1000000) (2376293 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (72126 / 1000000)
    false false 2 0 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSeventyEightThroughOneHundredEightyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredSeventyNinthLeaf :
    BennettGammaScaledIntervalCertificate (2376293 / 1000000) (2410001 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (72471 / 1000000)
    false false 2 0 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSeventyEightThroughOneHundredEightyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredEightiethLeaf :
    BennettGammaScaledIntervalCertificate (2410001 / 1000000) (2444217 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (72803 / 1000000)
    false false 2 0 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSeventyEightThroughOneHundredEightyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredEightyFirstLeaf :
    BennettGammaScaledIntervalCertificate (2444217 / 1000000) (2478952 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (73121 / 1000000)
    false false 2 0 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSeventyEightThroughOneHundredEightyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredEightySecondLeaf :
    BennettGammaScaledIntervalCertificate (2478952 / 1000000) (2514218 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (73425 / 1000000)
    false false 2 0 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredSeventyEightThroughOneHundredEightyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredEightyThirdLeaf :
    BennettGammaScaledIntervalCertificate (2514218 / 1000000) (2550028 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (73715 / 1000000)
    false false 2 0 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightyThreeThroughOneHundredEightySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredEightyFourthLeaf :
    BennettGammaScaledIntervalCertificate (2550028 / 1000000) (2586395 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (73990 / 1000000)
    false false 2 0 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightyThreeThroughOneHundredEightySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredEightyFifthLeaf :
    BennettGammaScaledIntervalCertificate (2586395 / 1000000) (2623333 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (74250 / 1000000)
    false true 2 0 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightyThreeThroughOneHundredEightySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredEightySixthLeaf :
    BennettGammaScaledIntervalCertificate (2623333 / 1000000) (2660858 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (74494 / 1000000)
    true true 2 0 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightyThreeThroughOneHundredEightySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredEightySeventhLeaf :
    BennettGammaScaledIntervalCertificate (2660858 / 1000000) (2698985 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (74722 / 1000000)
    true true 2 0 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightyThreeThroughOneHundredEightySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- One hundred eighty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstOneHundredEightySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (2698985 / 1000000) :=
  .split (2343082 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstOneHundredSeventySevenFiniteCertificateLeaves
    (.split (2376293 / 1000000) (by norm_num) (by norm_num) oneHundredSeventyEighthLeaf
      (.split (2410001 / 1000000) (by norm_num) (by norm_num) oneHundredSeventyNinthLeaf
        (.split (2444217 / 1000000) (by norm_num) (by norm_num) oneHundredEightiethLeaf
          (.split (2478952 / 1000000) (by norm_num) (by norm_num) oneHundredEightyFirstLeaf
            (.split (2514218 / 1000000) (by norm_num) (by norm_num) oneHundredEightySecondLeaf
              (.split (2550028 / 1000000) (by norm_num) (by norm_num) oneHundredEightyThirdLeaf
                (.split (2586395 / 1000000) (by norm_num) (by norm_num) oneHundredEightyFourthLeaf
                  (.split (2623333 / 1000000) (by norm_num) (by norm_num) oneHundredEightyFifthLeaf
                    (.split (2660858 / 1000000) (by norm_num) (by norm_num)
                      oneHundredEightySixthLeaf oneHundredEightySeventhLeaf)))))))))

private theorem leavesOneHundredEightyEightThroughOneHundredNinetyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (74933 / 1000000 : Real) true true 2 0 2 0
          (2698985 / 1000000) (2737730 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (75127 / 1000000 : Real) true true 2 0 2 0
          (2737730 / 1000000) (2777110 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (75303 / 1000000 : Real) true false 2 0 0 1
          (2777110 / 1000000) (2817138 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (75462 / 1000000 : Real) true false 2 0 0 1
          (2817138 / 1000000) (2857848 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (75602 / 1000000 : Real) true false 2 0 0 1
          (2857848 / 1000000) (2899257 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesOneHundredNinetyThreeThroughOneHundredNinetySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (75723 / 1000000 : Real) false false 0 1 0 1
          (2899257 / 1000000) (2941386 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (75825 / 1000000 : Real) false false 0 1 0 1
          (2941386 / 1000000) (2984258 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (75907 / 1000000 : Real) false false 0 1 0 1
          (2984258 / 1000000) (3027897 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (75968 / 1000000 : Real) false false 0 1 0 1
          (3027897 / 1000000) (3072328 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (76009 / 1000000 : Real) false false 0 1 0 1
          (3072328 / 1000000) (3117579 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def oneHundredEightyEighthLeaf :
    BennettGammaScaledIntervalCertificate (2698985 / 1000000) (2737730 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (74933 / 1000000)
    true true 2 0 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightyEightThroughOneHundredNinetyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredEightyNinthLeaf :
    BennettGammaScaledIntervalCertificate (2737730 / 1000000) (2777110 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (75127 / 1000000)
    true true 2 0 2 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightyEightThroughOneHundredNinetyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredNinetiethLeaf :
    BennettGammaScaledIntervalCertificate (2777110 / 1000000) (2817138 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (75303 / 1000000)
    true false 2 0 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightyEightThroughOneHundredNinetyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredNinetyFirstLeaf :
    BennettGammaScaledIntervalCertificate (2817138 / 1000000) (2857848 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (75462 / 1000000)
    true false 2 0 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightyEightThroughOneHundredNinetyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredNinetySecondLeaf :
    BennettGammaScaledIntervalCertificate (2857848 / 1000000) (2899257 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (75602 / 1000000)
    true false 2 0 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredEightyEightThroughOneHundredNinetyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredNinetyThirdLeaf :
    BennettGammaScaledIntervalCertificate (2899257 / 1000000) (2941386 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (75723 / 1000000)
    false false 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredNinetyThreeThroughOneHundredNinetySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredNinetyFourthLeaf :
    BennettGammaScaledIntervalCertificate (2941386 / 1000000) (2984258 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (75825 / 1000000)
    false false 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredNinetyThreeThroughOneHundredNinetySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredNinetyFifthLeaf :
    BennettGammaScaledIntervalCertificate (2984258 / 1000000) (3027897 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (75907 / 1000000)
    false false 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredNinetyThreeThroughOneHundredNinetySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredNinetySixthLeaf :
    BennettGammaScaledIntervalCertificate (3027897 / 1000000) (3072328 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (75968 / 1000000)
    false false 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredNinetyThreeThroughOneHundredNinetySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredNinetySeventhLeaf :
    BennettGammaScaledIntervalCertificate (3072328 / 1000000) (3117579 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (76009 / 1000000)
    false false 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredNinetyThreeThroughOneHundredNinetySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- One hundred ninety-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstOneHundredNinetySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (3117579 / 1000000) :=
  .split (2698985 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstOneHundredEightySevenFiniteCertificateLeaves
    (.split (2737730 / 1000000) (by norm_num) (by norm_num) oneHundredEightyEighthLeaf
      (.split (2777110 / 1000000) (by norm_num) (by norm_num) oneHundredEightyNinthLeaf
        (.split (2817138 / 1000000) (by norm_num) (by norm_num) oneHundredNinetiethLeaf
          (.split (2857848 / 1000000) (by norm_num) (by norm_num) oneHundredNinetyFirstLeaf
            (.split (2899257 / 1000000) (by norm_num) (by norm_num) oneHundredNinetySecondLeaf
              (.split (2941386 / 1000000) (by norm_num) (by norm_num) oneHundredNinetyThirdLeaf
                (.split (2984258 / 1000000) (by norm_num) (by norm_num) oneHundredNinetyFourthLeaf
                  (.split (3027897 / 1000000) (by norm_num) (by norm_num) oneHundredNinetyFifthLeaf
                    (.split (3072328 / 1000000) (by norm_num) (by norm_num)
                      oneHundredNinetySixthLeaf oneHundredNinetySeventhLeaf)))))))))

private theorem leavesOneHundredNinetyEightThroughTwoHundredTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (76028 / 1000000 : Real) false false 0 1 0 1
          (3117579 / 1000000) (3163679 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (76030 / 1000000 : Real) false false 0 1 0 1
          (3163679 / 1000000) (3181980 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (8 / 81 : Real) false true 0 1 0 1
          (3181980 / 1000000) (3181981 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (76030 / 1000000 : Real) true true 0 1 0 1
          (3181981 / 1000000) (3229314 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (76019 / 1000000 : Real) true true 0 1 0 1
          (3229314 / 1000000) (3277572 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesTwoHundredThreeThroughTwoHundredSevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (75985 / 1000000 : Real) true true 0 1 0 1
          (3277572 / 1000000) (3326790 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (75929 / 1000000 : Real) true true 0 1 0 1
          (3326790 / 1000000) (3377003 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (75849 / 1000000 : Real) true true 0 1 0 1
          (3377003 / 1000000) (3428247 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (75745 / 1000000 : Real) true true 0 1 0 1
          (3428247 / 1000000) (3480556 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (75616 / 1000000 : Real) true true 0 1 0 1
          (3480556 / 1000000) (3533960 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def oneHundredNinetyEighthLeaf :
    BennettGammaScaledIntervalCertificate (3117579 / 1000000) (3163679 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (76028 / 1000000)
    false false 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredNinetyEightThroughTwoHundredTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def oneHundredNinetyNinthLeaf :
    BennettGammaScaledIntervalCertificate (3163679 / 1000000) (3181980 / 1000000) :=
  bennettGammaIncreasingRationalLeaf _ _ (76030 / 1000000)
    false false 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredNinetyEightThroughTwoHundredTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredthLeaf :
    BennettGammaScaledIntervalCertificate (3181980 / 1000000) (3181981 / 1000000) :=
  bennettGammaUniformRationalLeaf _ _
    false true 0 1 0 1
    (by norm_num) (by norm_num)
    leavesOneHundredNinetyEightThroughTwoHundredTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFirstLeaf :
    BennettGammaScaledIntervalCertificate (3181981 / 1000000) (3229314 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (76030 / 1000000)
    true true 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredNinetyEightThroughTwoHundredTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredSecondLeaf :
    BennettGammaScaledIntervalCertificate (3229314 / 1000000) (3277572 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (76019 / 1000000)
    true true 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesOneHundredNinetyEightThroughTwoHundredTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredThirdLeaf :
    BennettGammaScaledIntervalCertificate (3277572 / 1000000) (3326790 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (75985 / 1000000)
    true true 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThreeThroughTwoHundredSevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFourthLeaf :
    BennettGammaScaledIntervalCertificate (3326790 / 1000000) (3377003 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (75929 / 1000000)
    true true 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThreeThroughTwoHundredSevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFifthLeaf :
    BennettGammaScaledIntervalCertificate (3377003 / 1000000) (3428247 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (75849 / 1000000)
    true true 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThreeThroughTwoHundredSevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredSixthLeaf :
    BennettGammaScaledIntervalCertificate (3428247 / 1000000) (3480556 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (75745 / 1000000)
    true true 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThreeThroughTwoHundredSevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredSeventhLeaf :
    BennettGammaScaledIntervalCertificate (3480556 / 1000000) (3533960 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (75616 / 1000000)
    true true 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThreeThroughTwoHundredSevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Two hundred seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstTwoHundredSevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (3533960 / 1000000) :=
  .split (3117579 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstOneHundredNinetySevenFiniteCertificateLeaves
    (.split (3163679 / 1000000) (by norm_num) (by norm_num) oneHundredNinetyEighthLeaf
      (.split (3181980 / 1000000) (by norm_num) (by norm_num) oneHundredNinetyNinthLeaf
        (.split (3181981 / 1000000) (by norm_num) (by norm_num) twoHundredthLeaf
          (.split (3229314 / 1000000) (by norm_num) (by norm_num) twoHundredFirstLeaf
            (.split (3277572 / 1000000) (by norm_num) (by norm_num) twoHundredSecondLeaf
              (.split (3326790 / 1000000) (by norm_num) (by norm_num) twoHundredThirdLeaf
                (.split (3377003 / 1000000) (by norm_num) (by norm_num) twoHundredFourthLeaf
                  (.split (3428247 / 1000000) (by norm_num) (by norm_num) twoHundredFifthLeaf
                    (.split (3480556 / 1000000) (by norm_num) (by norm_num)
                      twoHundredSixthLeaf twoHundredSeventhLeaf)))))))))

private theorem leavesTwoHundredEightThroughTwoHundredTwelveRationalValid :
    BennettGammaRationalIntervalBoxValid
        (75462 / 1000000 : Real) true true 0 1 0 1
          (3533960 / 1000000) (3588482 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (75283 / 1000000 : Real) true true 0 1 0 1
          (3588482 / 1000000) (3644130 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (75078 / 1000000 : Real) true false 0 1 1 0
          (3644130 / 1000000) (3701107 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (74846 / 1000000 : Real) true false 0 1 1 0
          (3701107 / 1000000) (3759461 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (74587 / 1000000 : Real) false false 1 0 1 0
          (3759461 / 1000000) (3819234 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesTwoHundredThirteenThroughTwoHundredSeventeenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (74300 / 1000000 : Real) false false 1 0 1 0
          (3819234 / 1000000) (3880478 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (73984 / 1000000 : Real) false false 1 0 1 0
          (3880478 / 1000000) (3943253 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (73639 / 1000000 : Real) false false 1 0 1 0
          (3943253 / 1000000) (4007628 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (73264 / 1000000 : Real) false false 1 0 1 0
          (4007628 / 1000000) (4073678 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (72859 / 1000000 : Real) false false 1 0 1 0
          (4073678 / 1000000) (4141486 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def twoHundredEighthLeaf :
    BennettGammaScaledIntervalCertificate (3533960 / 1000000) (3588482 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (75462 / 1000000)
    true true 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredEightThroughTwoHundredTwelveRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredNinthLeaf :
    BennettGammaScaledIntervalCertificate (3588482 / 1000000) (3644130 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (75283 / 1000000)
    true true 0 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredEightThroughTwoHundredTwelveRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredTenthLeaf :
    BennettGammaScaledIntervalCertificate (3644130 / 1000000) (3701107 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (75078 / 1000000)
    true false 0 1 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredEightThroughTwoHundredTwelveRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredEleventhLeaf :
    BennettGammaScaledIntervalCertificate (3701107 / 1000000) (3759461 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (74846 / 1000000)
    true false 0 1 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredEightThroughTwoHundredTwelveRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredTwelfthLeaf :
    BennettGammaScaledIntervalCertificate (3759461 / 1000000) (3819234 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (74587 / 1000000)
    false false 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredEightThroughTwoHundredTwelveRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredThirteenthLeaf :
    BennettGammaScaledIntervalCertificate (3819234 / 1000000) (3880478 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (74300 / 1000000)
    false false 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirteenThroughTwoHundredSeventeenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFourteenthLeaf :
    BennettGammaScaledIntervalCertificate (3880478 / 1000000) (3943253 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (73984 / 1000000)
    false false 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirteenThroughTwoHundredSeventeenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFifteenthLeaf :
    BennettGammaScaledIntervalCertificate (3943253 / 1000000) (4007628 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (73639 / 1000000)
    false false 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirteenThroughTwoHundredSeventeenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredSixteenthLeaf :
    BennettGammaScaledIntervalCertificate (4007628 / 1000000) (4073678 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (73264 / 1000000)
    false false 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirteenThroughTwoHundredSeventeenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredSeventeenthLeaf :
    BennettGammaScaledIntervalCertificate (4073678 / 1000000) (4141486 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (72859 / 1000000)
    false false 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirteenThroughTwoHundredSeventeenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Two hundred seventeen checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstTwoHundredSeventeenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (4141486 / 1000000) :=
  .split (3533960 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstTwoHundredSevenFiniteCertificateLeaves
    (.split (3588482 / 1000000) (by norm_num) (by norm_num) twoHundredEighthLeaf
      (.split (3644130 / 1000000) (by norm_num) (by norm_num) twoHundredNinthLeaf
        (.split (3701107 / 1000000) (by norm_num) (by norm_num) twoHundredTenthLeaf
          (.split (3759461 / 1000000) (by norm_num) (by norm_num) twoHundredEleventhLeaf
            (.split (3819234 / 1000000) (by norm_num) (by norm_num) twoHundredTwelfthLeaf
              (.split (3880478 / 1000000) (by norm_num) (by norm_num) twoHundredThirteenthLeaf
                (.split (3943253 / 1000000) (by norm_num) (by norm_num) twoHundredFourteenthLeaf
                  (.split (4007628 / 1000000) (by norm_num) (by norm_num) twoHundredFifteenthLeaf
                    (.split (4073678 / 1000000) (by norm_num) (by norm_num)
                      twoHundredSixteenthLeaf twoHundredSeventeenthLeaf)))))))))

private theorem leavesTwoHundredEighteenThroughTwoHundredTwentyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (72423 / 1000000 : Real) false false 1 0 1 0
          (4141486 / 1000000) (4211141 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (71956 / 1000000 : Real) false false 1 0 1 0
          (4211141 / 1000000) (4282740 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (71456 / 1000000 : Real) false false 1 0 1 0
          (4282740 / 1000000) (4356387 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (70924 / 1000000 : Real) false false 1 0 1 0
          (4356387 / 1000000) (4432194 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (70358 / 1000000 : Real) false true 1 0 1 0
          (4432194 / 1000000) (4510283 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesTwoHundredTwentyThreeThroughTwoHundredTwentySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (69758 / 1000000 : Real) true true 1 0 1 0
          (4510283 / 1000000) (4590785 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (69124 / 1000000 : Real) true true 1 0 1 0
          (4590785 / 1000000) (4673841 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (68453 / 1000000 : Real) true true 1 0 1 0
          (4673841 / 1000000) (4759605 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (67747 / 1000000 : Real) true true 1 0 1 0
          (4759605 / 1000000) (4848240 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (67004 / 1000000 : Real) true true 1 0 1 0
          (4848240 / 1000000) (4939919 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def twoHundredEighteenthLeaf :
    BennettGammaScaledIntervalCertificate (4141486 / 1000000) (4211141 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (72423 / 1000000)
    false false 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredEighteenThroughTwoHundredTwentyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredNineteenthLeaf :
    BennettGammaScaledIntervalCertificate (4211141 / 1000000) (4282740 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (71956 / 1000000)
    false false 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredEighteenThroughTwoHundredTwentyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredTwentiethLeaf :
    BennettGammaScaledIntervalCertificate (4282740 / 1000000) (4356387 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (71456 / 1000000)
    false false 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredEighteenThroughTwoHundredTwentyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredTwentyFirstLeaf :
    BennettGammaScaledIntervalCertificate (4356387 / 1000000) (4432194 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (70924 / 1000000)
    false false 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredEighteenThroughTwoHundredTwentyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredTwentySecondLeaf :
    BennettGammaScaledIntervalCertificate (4432194 / 1000000) (4510283 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (70358 / 1000000)
    false true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredEighteenThroughTwoHundredTwentyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredTwentyThirdLeaf :
    BennettGammaScaledIntervalCertificate (4510283 / 1000000) (4590785 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (69758 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredTwentyThreeThroughTwoHundredTwentySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredTwentyFourthLeaf :
    BennettGammaScaledIntervalCertificate (4590785 / 1000000) (4673841 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (69124 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredTwentyThreeThroughTwoHundredTwentySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredTwentyFifthLeaf :
    BennettGammaScaledIntervalCertificate (4673841 / 1000000) (4759605 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (68453 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredTwentyThreeThroughTwoHundredTwentySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredTwentySixthLeaf :
    BennettGammaScaledIntervalCertificate (4759605 / 1000000) (4848240 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (67747 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredTwentyThreeThroughTwoHundredTwentySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredTwentySeventhLeaf :
    BennettGammaScaledIntervalCertificate (4848240 / 1000000) (4939919 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (67004 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredTwentyThreeThroughTwoHundredTwentySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Two hundred twenty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstTwoHundredTwentySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (4939919 / 1000000) :=
  .split (4141486 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstTwoHundredSeventeenFiniteCertificateLeaves
    (.split (4211141 / 1000000) (by norm_num) (by norm_num) twoHundredEighteenthLeaf
      (.split (4282740 / 1000000) (by norm_num) (by norm_num) twoHundredNineteenthLeaf
        (.split (4356387 / 1000000) (by norm_num) (by norm_num) twoHundredTwentiethLeaf
          (.split (4432194 / 1000000) (by norm_num) (by norm_num) twoHundredTwentyFirstLeaf
            (.split (4510283 / 1000000) (by norm_num) (by norm_num) twoHundredTwentySecondLeaf
              (.split (4590785 / 1000000) (by norm_num) (by norm_num) twoHundredTwentyThirdLeaf
                (.split (4673841 / 1000000) (by norm_num) (by norm_num) twoHundredTwentyFourthLeaf
                  (.split (4759605 / 1000000) (by norm_num) (by norm_num) twoHundredTwentyFifthLeaf
                    (.split (4848240 / 1000000) (by norm_num) (by norm_num)
                      twoHundredTwentySixthLeaf twoHundredTwentySeventhLeaf)))))))))

private theorem leavesTwoHundredTwentyEightThroughTwoHundredThirtyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (66223 / 1000000 : Real) true true 1 0 1 0
          (4939919 / 1000000) (5034484 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (65408 / 1000000 : Real) true true 1 0 1 0
          (5034484 / 1000000) (5132520 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (64553 / 1000000 : Real) true true 1 0 1 0
          (5132520 / 1000000) (5234200 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (63659 / 1000000 : Real) true true 1 0 1 0
          (5234200 / 1000000) (5339680 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (62728 / 1000000 : Real) true true 1 0 1 0
          (5339680 / 1000000) (5449074 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private theorem leavesTwoHundredThirtyThreeThroughTwoHundredThirtySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (61756 / 1000000 : Real) true true 1 0 1 0
          (5449074 / 1000000) (5562431 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (60749 / 1000000 : Real) true true 1 0 1 0
          (5562431 / 1000000) (5679691 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (59709 / 1000000 : Real) true true 1 0 1 0
          (5679691 / 1000000) (5800641 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (58639 / 1000000 : Real) true true 1 0 1 0
          (5800641 / 1000000) (5924851 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (57547 / 1000000 : Real) true true 1 0 1 0
          (5924851 / 1000000) (6051616 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def twoHundredTwentyEighthLeaf :
    BennettGammaScaledIntervalCertificate (4939919 / 1000000) (5034484 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (66223 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredTwentyEightThroughTwoHundredThirtyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredTwentyNinthLeaf :
    BennettGammaScaledIntervalCertificate (5034484 / 1000000) (5132520 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (65408 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredTwentyEightThroughTwoHundredThirtyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredThirtiethLeaf :
    BennettGammaScaledIntervalCertificate (5132520 / 1000000) (5234200 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (64553 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredTwentyEightThroughTwoHundredThirtyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredThirtyFirstLeaf :
    BennettGammaScaledIntervalCertificate (5234200 / 1000000) (5339680 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (63659 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredTwentyEightThroughTwoHundredThirtyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredThirtySecondLeaf :
    BennettGammaScaledIntervalCertificate (5339680 / 1000000) (5449074 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (62728 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredTwentyEightThroughTwoHundredThirtyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredThirtyThirdLeaf :
    BennettGammaScaledIntervalCertificate (5449074 / 1000000) (5562431 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (61756 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirtyThreeThroughTwoHundredThirtySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredThirtyFourthLeaf :
    BennettGammaScaledIntervalCertificate (5562431 / 1000000) (5679691 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (60749 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirtyThreeThroughTwoHundredThirtySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredThirtyFifthLeaf :
    BennettGammaScaledIntervalCertificate (5679691 / 1000000) (5800641 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (59709 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirtyThreeThroughTwoHundredThirtySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredThirtySixthLeaf :
    BennettGammaScaledIntervalCertificate (5800641 / 1000000) (5924851 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (58639 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirtyThreeThroughTwoHundredThirtySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredThirtySeventhLeaf :
    BennettGammaScaledIntervalCertificate (5924851 / 1000000) (6051616 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (57547 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirtyThreeThroughTwoHundredThirtySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- Two hundred thirty-seven checked adjacent leaves at the lower endpoint. -/
def bennettGammaFirstTwoHundredThirtySevenFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) (6051616 / 1000000) :=
  .split (4939919 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstTwoHundredTwentySevenFiniteCertificateLeaves
    (.split (5034484 / 1000000) (by norm_num) (by norm_num) twoHundredTwentyEighthLeaf
      (.split (5132520 / 1000000) (by norm_num) (by norm_num) twoHundredTwentyNinthLeaf
        (.split (5234200 / 1000000) (by norm_num) (by norm_num) twoHundredThirtiethLeaf
          (.split (5339680 / 1000000) (by norm_num) (by norm_num) twoHundredThirtyFirstLeaf
            (.split (5449074 / 1000000) (by norm_num) (by norm_num) twoHundredThirtySecondLeaf
              (.split (5562431 / 1000000) (by norm_num) (by norm_num) twoHundredThirtyThirdLeaf
                (.split (5679691 / 1000000) (by norm_num) (by norm_num) twoHundredThirtyFourthLeaf
                  (.split (5800641 / 1000000) (by norm_num) (by norm_num) twoHundredThirtyFifthLeaf
                    (.split (5924851 / 1000000) (by norm_num) (by norm_num)
                      twoHundredThirtySixthLeaf twoHundredThirtySeventhLeaf)))))))))

/- The remaining thirteen exact leaves are retained here while they are moved
to a focused completion module; keeping the verified 237-leaf prefix active
avoids re-elaborating the whole certificate beyond the process limit. -/

/-
private theorem leavesTwoHundredThirtyEightThroughTwoHundredFortyTwoRationalValid :
    BennettGammaRationalIntervalBoxValid
        (56440 / 1000000 : Real) true true 1 0 1 0
          (6051616 / 1000000) (6179896 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (55331 / 1000000 : Real) true true 1 0 1 0
          (6179896 / 1000000) (6308287 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (54233 / 1000000 : Real) true true 1 0 1 0
          (6308287 / 1000000) (6435037 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (53163 / 1000000 : Real) true true 1 0 1 0
          (6435037 / 1000000) (6558127 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (52139 / 1000000 : Real) true false 1 0 0 0
          (6558127 / 1000000) (6679233 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def twoHundredThirtyEighthLeaf :
    BennettGammaScaledIntervalCertificate (6051616 / 1000000) (6179896 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (56440 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirtyEightThroughTwoHundredFortyTwoRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredThirtyNinthLeaf :
    BennettGammaScaledIntervalCertificate (6179896 / 1000000) (6308287 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (55331 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirtyEightThroughTwoHundredFortyTwoRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFortiethLeaf :
    BennettGammaScaledIntervalCertificate (6308287 / 1000000) (6435037 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (54233 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirtyEightThroughTwoHundredFortyTwoRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFortyFirstLeaf :
    BennettGammaScaledIntervalCertificate (6435037 / 1000000) (6558127 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (53163 / 1000000)
    true true 1 0 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirtyEightThroughTwoHundredFortyTwoRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFortySecondLeaf :
    BennettGammaScaledIntervalCertificate (6558127 / 1000000) (6679233 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (52139 / 1000000)
    true false 1 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredThirtyEightThroughTwoHundredFortyTwoRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private theorem leavesTwoHundredFortyThreeThroughTwoHundredFortySevenRationalValid :
    BennettGammaRationalIntervalBoxValid
        (51145 / 1000000 : Real) true false 1 0 0 0
          (6679233 / 1000000) (6814352 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (50054 / 1000000 : Real) true false 1 0 0 0
          (6814352 / 1000000) (6964140 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (48869 / 1000000 : Real) true false 1 0 0 0
          (6964140 / 1000000) (7129320 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (47590 / 1000000 : Real) false false 0 0 0 0
          (7129320 / 1000000) (7310744 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (46222 / 1000000 : Real) false false 0 0 0 0
          (7310744 / 1000000) (7509458 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def twoHundredFortyThirdLeaf :
    BennettGammaScaledIntervalCertificate (6679233 / 1000000) (6814352 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (51145 / 1000000)
    true false 1 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredFortyThreeThroughTwoHundredFortySevenRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFortyFourthLeaf :
    BennettGammaScaledIntervalCertificate (6814352 / 1000000) (6964140 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (50054 / 1000000)
    true false 1 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredFortyThreeThroughTwoHundredFortySevenRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFortyFifthLeaf :
    BennettGammaScaledIntervalCertificate (6964140 / 1000000) (7129320 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (48869 / 1000000)
    true false 1 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredFortyThreeThroughTwoHundredFortySevenRationalValid.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFortySixthLeaf :
    BennettGammaScaledIntervalCertificate (7129320 / 1000000) (7310744 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (47590 / 1000000)
    false false 0 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredFortyThreeThroughTwoHundredFortySevenRationalValid.2.2.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFortySeventhLeaf :
    BennettGammaScaledIntervalCertificate (7310744 / 1000000) (7509458 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (46222 / 1000000)
    false false 0 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredFortyThreeThroughTwoHundredFortySevenRationalValid.2.2.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private theorem leavesTwoHundredFortyEightThroughTwoHundredFiftyRationalValid :
    BennettGammaRationalIntervalBoxValid
        (44769 / 1000000 : Real) false false 0 0 0 0
          (7509458 / 1000000) (7726777 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (43233 / 1000000 : Real) false false 0 0 0 0
          (7726777 / 1000000) (7964367 / 1000000) ∧
      BennettGammaRationalIntervalBoxValid
        (41617 / 1000000 : Real) false false 0 0 0 0
          (7964367 / 1000000) (8000000 / 1000000) := by
  repeat' first | constructor
  all_goals
    norm_num [BennettGammaRationalIntervalBoxValid,
      bennettGammaRationalLowerIntervalBox, bennettGammaRationalUpperIntervalBox,
      bennettGammaIntervalRationalComponent, bennettGammaArctanEndpointLower,
      bennettGammaArctanEndpointUpper, bennettGammaMixedLogEndpointLowerWithMode,
      bennettGammaMixedLogEndpointUpperWithMode, bennettGammaMixedLogEndpointLower,
      bennettGammaMixedLogEndpointUpper, bennettGammaMixedLogInverseEndpointLower,
      bennettGammaMixedLogInverseEndpointUpper, arctanSepticPolynomial,
      arctanNonicPolynomial, logQuarticPolynomial, logQuinticPolynomial]
    field_simp [Real.pi_pos.ne']
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]

private def twoHundredFortyEighthLeaf :
    BennettGammaScaledIntervalCertificate (7509458 / 1000000) (7726777 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (44769 / 1000000)
    false false 0 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredFortyEightThroughTwoHundredFiftyRationalValid.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFortyNinthLeaf :
    BennettGammaScaledIntervalCertificate (7726777 / 1000000) (7964367 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (43233 / 1000000)
    false false 0 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredFortyEightThroughTwoHundredFiftyRationalValid.2.1
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

private def twoHundredFiftiethLeaf :
    BennettGammaScaledIntervalCertificate (7964367 / 1000000) (8000000 / 1000000) :=
  bennettGammaDecreasingRationalLeaf _ _ (41617 / 1000000)
    false false 0 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    leavesTwoHundredFortyEightThroughTwoHundredFiftyRationalValid.2.2
    (by norm_num [BennettGammaMixedLogScaleValid])
    (by norm_num [BennettGammaMixedLogScaleValid])

/-- All two hundred fifty rational leaves from `5/7` through the endpoint `8`. -/
def bennettGammaFirstTwoHundredFiftyFiniteCertificateLeaves :
    BennettGammaScaledIntervalCertificate ((5 : Real) / 7) 8 :=
  .split (6051616 / 1000000) (by norm_num) (by norm_num)
    bennettGammaFirstTwoHundredThirtySevenFiniteCertificateLeaves
    (.split (6179896 / 1000000) (by norm_num) (by norm_num) twoHundredThirtyEighthLeaf
      (.split (6308287 / 1000000) (by norm_num) (by norm_num) twoHundredThirtyNinthLeaf
        (.split (6435037 / 1000000) (by norm_num) (by norm_num) twoHundredFortiethLeaf
          (.split (6558127 / 1000000) (by norm_num) (by norm_num) twoHundredFortyFirstLeaf
            (.split (6679233 / 1000000) (by norm_num) (by norm_num) twoHundredFortySecondLeaf
              (.split (6814352 / 1000000) (by norm_num) (by norm_num) twoHundredFortyThirdLeaf
                (.split (6964140 / 1000000) (by norm_num) (by norm_num) twoHundredFortyFourthLeaf
                  (.split (7129320 / 1000000) (by norm_num) (by norm_num) twoHundredFortyFifthLeaf
                    (.split (7310744 / 1000000) (by norm_num) (by norm_num) twoHundredFortySixthLeaf
                      (.split (7509458 / 1000000) (by norm_num) (by norm_num) twoHundredFortySeventhLeaf
                        (.split (7726777 / 1000000) (by norm_num) (by norm_num) twoHundredFortyEighthLeaf
                          (.split (7964367 / 1000000) (by norm_num) (by norm_num)
                            twoHundredFortyNinthLeaf (by simpa using twoHundredFiftiethLeaf))))))))))))
-/

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
