import RiemannHypothesisProject.RiemannVonMangoldt.BellottiWongGammaFiniteCertificate

/-!
# Completion of Bennett's compact Gamma interval certificate

The final thirteen rational leaves of the published compact interval
certificate.  Keeping them in this focused module lets Lean elaborate the
finite endpoint arithmetic independently of the established 237-leaf prefix.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

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

/-- The complete 250-leaf rational certificate on Bennett's compact interval. -/
def bennettGammaFiniteCertificateLeaves :
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
                            twoHundredFortyNinthLeaf
                            (by
                              convert twoHundredFiftiethLeaf using 1 <;>
                                norm_num)))))))))))))

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
