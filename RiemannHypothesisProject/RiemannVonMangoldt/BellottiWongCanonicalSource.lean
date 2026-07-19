import RiemannHypothesisProject.RiemannVonMangoldt.CanonicalMultiplicityCount
import RiemannHypothesisProject.RiemannVonMangoldt.BellottiWongFirstRowParameters
import RiemannHypothesisProject.RiemannVonMangoldt.BellottiWongGammaFiniteCertificateCompletion

/-!
# Bellotti-Wong canonical source assembly

Bellotti-Wong prove their published `N(T)` estimate in two height ranges.  The
large-height range is obtained by specializing their general theorem and its
first row of numerical parameters.  The remaining finite range uses Platt's
verified bound for `S(T)` together with the explicit Riemann-von Mangoldt
identity.

This module records those two source-shaped inputs separately and checks the
elementary assembly into `BellottiWongCanonicalMultiplicityNTTheorem`.  In
particular, the finite-range numerical constant is proved below to fit inside
the published error term on the whole stated domain `T >= exp 1`.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/--
The uniform finite-range constant obtained in the paper from Platt's
`|S(T)| <= 2.5167` computation, the `g(T)` remainder estimate, and the
Riemann-von Mangoldt constant term.
-/
def bellottiWongPlattLowRangeConstant : Real :=
  ((25167 : Real) / 10000) + 1 / (50 * Real.exp 1) + 7 / 8

/-- The alternative logarithmic branch in Bellotti-Wong's first table row. -/
def bellottiWongFirstRowAlternativeErrorTerm (T : Real) : Real :=
  ((168845 : Real) / 100000) * Real.log (Real.log T) +
    ((238456 : Real) / 100000)

/--
The complete first-row error expression obtained from Bellotti-Wong's general
theorem.  Their final theorem selects the first entry of this minimum.
-/
def bellottiWongFirstRowGeneralErrorTerm (T : Real) : Real :=
  ((10076 : Real) / 100000) * Real.log T +
    min
      (((24460 : Real) / 100000) * Real.log (Real.log T) +
        ((808344 : Real) / 100000))
      (bellottiWongFirstRowAlternativeErrorTerm T)

/--
The first-row large-height specialization of Bellotti-Wong's general theorem,
including both branches of the published minimum and stated in the project's
canonical analytic-multiplicity normalization.
-/
def BellottiWongFirstRowGeneralTheoremEstimate : Prop :=
  forall T : Real,
    bellottiWongHighRangeThreshold <= T ->
      |canonicalPositiveOrdinateZetaZeroMultiplicityCount T -
          riemannVonMangoldtMainTerm T| <=
        bellottiWongFirstRowGeneralErrorTerm T

/-- The first branch of the general-theorem table row gives the advertised error. -/
theorem BellottiWongFirstRowGeneralTheoremEstimate.toHighRangeEstimate
    (hgeneral : BellottiWongFirstRowGeneralTheoremEstimate) :
    forall T : Real,
      bellottiWongHighRangeThreshold <= T ->
        |canonicalPositiveOrdinateZetaZeroMultiplicityCount T -
            riemannVonMangoldtMainTerm T| <=
          bellottiWongErrorTerm T := by
  intro T hT
  exact (hgeneral T hT).trans (by
    unfold bellottiWongFirstRowGeneralErrorTerm bellottiWongErrorTerm
    calc
      ((10076 : Real) / 100000) * Real.log T +
          min
            (((24460 : Real) / 100000) * Real.log (Real.log T) +
              ((808344 : Real) / 100000))
            (bellottiWongFirstRowAlternativeErrorTerm T) <=
          ((10076 : Real) / 100000) * Real.log T +
            (((24460 : Real) / 100000) * Real.log (Real.log T) +
              ((808344 : Real) / 100000)) :=
        add_le_add le_rfl (min_le_left _ _)
      _ = ((10076 : Real) / 100000) * Real.log T +
            ((24460 : Real) / 100000) * Real.log (Real.log T) +
              ((808344 : Real) / 100000) := by ring)

/--
The three source ingredients used by Bellotti-Wong below their large-height
threshold.  `argumentTerm` is the paper's `S(T)`, while its `g(T)` is the
concrete branch-normalized `bellottiWongGammaRemainder`.  Keeping the exact
Riemann-von Mangoldt identity separate from the two bounds exposes the
argument-principle normalization instead of assuming the already assembled
low-range estimate.
-/
structure BellottiWongCanonicalLowRangeInputs where
  argumentTerm : Real -> Real
  riemannVonMangoldtIdentity :
    forall T : Real,
      bellottiWongValidFrom <= T ->
        T <= bellottiWongHighRangeThreshold ->
          canonicalPositiveOrdinateZetaZeroMultiplicityCount T =
            argumentTerm T + riemannVonMangoldtMainTerm T + 7 / 8 +
              bellottiWongGammaRemainder T / 2
  plattArgumentTermBound :
    forall T : Real,
      0 <= T ->
        T <= bellottiWongHighRangeThreshold ->
          |argumentTerm T| <= (25167 : Real) / 10000
  gammaScaledStirlingEnvelope : BennettGammaScaledStirlingEnvelope

/--
The finite-height computational part of Bellotti-Wong's proof, after the
argument-principle `N(T)` has been identified with the project's canonical
analytic-multiplicity count.
-/
def BellottiWongPlattLowRangeEstimate : Prop :=
  forall T : Real,
    bellottiWongValidFrom <= T ->
      T <= bellottiWongHighRangeThreshold ->
        |canonicalPositiveOrdinateZetaZeroMultiplicityCount T -
            riemannVonMangoldtMainTerm T| <=
          bellottiWongPlattLowRangeConstant

/-- The two genuinely analytic/computational inputs used in the published proof. -/
structure BellottiWongCanonicalSourceInputs where
  highRange : BellottiWongFirstRowGeneralTheoremEstimate
  lowRange : BellottiWongCanonicalLowRangeInputs

/--
Bellotti-Wong's exact finite-range identity, Platt bound, and gamma remainder
bound imply the assembled finite-range estimate.  This is the whole
finite-height derivation appearing in the proof of their main theorem.
-/
theorem BellottiWongCanonicalLowRangeInputs.toPlattLowRangeEstimate
    (source : BellottiWongCanonicalLowRangeInputs) :
    BellottiWongPlattLowRangeEstimate := by
  intro T hT hupper
  have hT_pos : 0 < T := by
    rw [bellottiWongValidFrom] at hT
    exact (Real.exp_pos 1).trans_le hT
  have hT_nonneg : 0 <= T := hT_pos.le
  have hfive_sevenths : (5 : Real) / 7 <= T := by
    have hexp_two : (2 : Real) < Real.exp 1 := Real.exp_one_gt_two
    rw [bellottiWongValidFrom] at hT
    norm_num at hexp_two ⊢
    linarith
  have hS := source.plattArgumentTermBound T hT_nonneg hupper
  have hg := bellottiWongGammaRemainder_abs_le_of_scaled_envelopes
    source.gammaScaledStirlingEnvelope
      (bennettGammaScaledIntervalEstimate_of_compact
        (bennettGammaCompactScaledIntervalEstimate_of_certificate
          bennettGammaFiniteCertificateLeaves))
      hfive_sevenths
  have hgammaHalf :
      |bellottiWongGammaRemainder T / 2| <= 1 / (50 * T) := by
    calc
      |bellottiWongGammaRemainder T / 2| =
          |bellottiWongGammaRemainder T| / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
      _ <= (1 / (25 * T)) / 2 := by gcongr
      _ = 1 / (50 * T) := by ring
  have hden_pos : 0 < 50 * Real.exp 1 := by positivity
  have hden_le : 50 * Real.exp 1 <= 50 * T := by
    rw [bellottiWongValidFrom] at hT
    nlinarith
  have hgammaUniform :
      |bellottiWongGammaRemainder T / 2| <= 1 / (50 * Real.exp 1) := by
    exact hgammaHalf.trans (one_div_le_one_div_of_le hden_pos hden_le)
  rw [source.riemannVonMangoldtIdentity T hT hupper]
  have htriangle :
      |source.argumentTerm T + riemannVonMangoldtMainTerm T + 7 / 8 +
          bellottiWongGammaRemainder T / 2 - riemannVonMangoldtMainTerm T| <=
        |source.argumentTerm T| + |(7 / 8 : Real)| +
          |bellottiWongGammaRemainder T / 2| := by
    calc
      |source.argumentTerm T + riemannVonMangoldtMainTerm T + 7 / 8 +
          bellottiWongGammaRemainder T / 2 - riemannVonMangoldtMainTerm T| =
          |source.argumentTerm T + 7 / 8 +
            bellottiWongGammaRemainder T / 2| := by
        congr 1
        ring
      _ <= |source.argumentTerm T + (7 / 8 : Real)| +
          |bellottiWongGammaRemainder T / 2| := abs_add_le _ _
      _ <= |source.argumentTerm T| + |(7 / 8 : Real)| +
          |bellottiWongGammaRemainder T / 2| :=
        add_le_add (abs_add_le _ _) le_rfl
  calc
    |source.argumentTerm T + riemannVonMangoldtMainTerm T + 7 / 8 +
        bellottiWongGammaRemainder T / 2 - riemannVonMangoldtMainTerm T| <=
        |source.argumentTerm T| + |(7 / 8 : Real)| +
          |bellottiWongGammaRemainder T / 2| := htriangle
    _ <= (25167 : Real) / 10000 + |(7 / 8 : Real)| +
          1 / (50 * Real.exp 1) :=
      add_le_add (add_le_add hS le_rfl) hgammaUniform
    _ = bellottiWongPlattLowRangeConstant := by
      unfold bellottiWongPlattLowRangeConstant
      rw [abs_of_nonneg (by norm_num : (0 : Real) <= 7 / 8)]
      ring

/--
The finite-range constant is strictly smaller than the published error term
throughout Bellotti-Wong's stated domain.  The proof only uses monotonicity of
the logarithm and coarse rational arithmetic; it does not assume a zero-count
estimate.
-/
theorem bellottiWongPlattLowRangeConstant_le_errorTerm
    {T : Real} (hT : bellottiWongValidFrom <= T) :
    bellottiWongPlattLowRangeConstant <= bellottiWongErrorTerm T := by
  have hexp_one : 1 <= Real.exp 1 := Real.one_le_exp zero_le_one
  have hlogT : 1 <= Real.log T := by
    rw [bellottiWongValidFrom] at hT
    calc
      (1 : Real) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ <= Real.log T := Real.log_le_log (by positivity) hT
  have hloglogT : 0 <= Real.log (Real.log T) :=
    Real.log_nonneg hlogT
  have hden : 1 <= 50 * Real.exp 1 := by nlinarith
  have hfrac : 1 / (50 * Real.exp 1) <= 1 := by
    exact (div_le_one (by positivity)).2 hden
  have hfirst :
      0 <= ((10076 : Real) / 100000) * Real.log T := by positivity
  have hsecond :
      0 <= ((24460 : Real) / 100000) * Real.log (Real.log T) := by
    positivity
  unfold bellottiWongPlattLowRangeConstant bellottiWongErrorTerm
  norm_num at hfirst hsecond hfrac ⊢
  linarith

/--
The paper's two source ranges imply the exact canonical published theorem.  The
height split and the low-range comparison are discharged here, leaving only
the source theorem and verified-computation inputs visible.
-/
theorem BellottiWongCanonicalSourceInputs.toCanonicalMultiplicityNTTheorem
    (source : BellottiWongCanonicalSourceInputs) :
    BellottiWongCanonicalMultiplicityNTTheorem := by
  intro T hT
  by_cases hhigh : bellottiWongHighRangeThreshold <= T
  · exact source.highRange.toHighRangeEstimate T hhigh
  · exact
      (source.lowRange.toPlattLowRangeEstimate T hT (le_of_not_ge hhigh)).trans
        (bellottiWongPlattLowRangeConstant_le_errorTerm hT)

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
