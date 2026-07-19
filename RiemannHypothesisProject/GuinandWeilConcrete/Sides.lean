import RiemannHypothesisProject.GuinandWeilFormulaTarget
import RiemannHypothesisProject.GlobalZeroSide
import RiemannHypothesisProject.SchwartzRiemannWeilWeight
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Concrete Guinand-Weil formula side definitions

This module contains the concrete zero, prime, pole, gamma, and residual side
definitions, plus the project/source side-data normalization records and finite
cutoff identity/error targets for the Guinand-Weil formula route.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open Filter
open scoped BigOperators
open scoped Topology

noncomputable section

/-- A finite zero window for the concrete Guinand-Weil cutoff formula. -/
abbrev GuinandWeilZeroWindow := Nat -> Finset ZetaZeroSubtype

/--
The real truncated zero side: sum the real zero contribution over the chosen
finite zero window.
-/
def guinandWeilTruncatedZeroSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (cutoff : Nat)
    (f : SchwartzLineTestFunction) : Real :=
  (zeroWindow cutoff).sum (fun rho : ZetaZeroSubtype => system.weight f rho)

/-- The limiting zero side attached to the concrete Riemann-Weil weight. -/
def guinandWeilZeroSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) : Real :=
  ∑' rho : ZetaZeroSubtype, system.weight f rho

/--
The real truncated zero side in the completed-zeta normalized convention:
project-known trivial zeroes contribute zero on the zero side.
-/
def guinandWeilTruncatedCompletedZetaNormalizedZeroSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (cutoff : Nat)
    (f : SchwartzLineTestFunction) : Real :=
  (zeroWindow cutoff).sum
    (fun rho : ZetaZeroSubtype =>
      completedZetaNormalizedZeroWeight system f rho)

/--
The nontrivial-zero subwindow of a concrete Guinand-Weil zero window.
-/
noncomputable def guinandWeilNontrivialZeroWindow
    (zeroWindow : GuinandWeilZeroWindow)
    (cutoff : Nat) : Finset ZetaZeroSubtype := by
  classical
  exact
    (zeroWindow cutoff).filter
      (fun rho : ZetaZeroSubtype =>
        Not (IsTrivialZetaZero (rho : Complex)))

/--
The limiting zero side in the completed-zeta normalized convention.
-/
def guinandWeilCompletedZetaNormalizedZeroSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) : Real :=
  tsum
    (fun rho : ZetaZeroSubtype =>
      completedZetaNormalizedZeroWeight system f rho)

/--
The completed-zeta normalized limiting zero side is the `tsum` over the
nontrivial-zero subtype of the original project weight.
-/
theorem guinandWeilCompletedZetaNormalizedZeroSide_eq_tsum_nontrivialZetaZeroWeight
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    guinandWeilCompletedZetaNormalizedZeroSide system f =
      tsum (nontrivialZetaZeroWeight system f) := by
  unfold guinandWeilCompletedZetaNormalizedZeroSide
  exact
    tsum_completedZetaNormalizedZeroWeight_eq_tsum_nontrivialZetaZeroWeight
      system f

/--
Finite normalized zero windows sum only nontrivial zero contributions.
-/
theorem guinandWeilTruncatedCompletedZetaNormalizedZeroSide_eq_sum_nontrivial
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (cutoff : Nat)
    (f : SchwartzLineTestFunction) :
    guinandWeilTruncatedCompletedZetaNormalizedZeroSide
        system zeroWindow cutoff f =
      (guinandWeilNontrivialZeroWindow zeroWindow cutoff).sum
        (fun rho : ZetaZeroSubtype => system.weight f rho) := by
  classical
  unfold guinandWeilTruncatedCompletedZetaNormalizedZeroSide
  unfold guinandWeilNontrivialZeroWindow
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho _hrho
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · simp [completedZetaNormalizedZeroWeight, htrivial]
  · simp [completedZetaNormalizedZeroWeight, htrivial]

/--
If the raw project weight already vanishes on project-known trivial zeroes,
then the raw and completed-zeta normalized finite zero sides agree.
-/
theorem guinandWeilTruncatedCompletedZetaNormalizedZeroSide_eq_truncatedZeroSide_of_trivialWeight_eq_zero
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (cutoff : Nat)
    (f : SchwartzLineTestFunction)
    (htrivial_weight :
      forall rho : ZetaZeroSubtype,
        IsTrivialZetaZero (rho : Complex) -> system.weight f rho = 0) :
    guinandWeilTruncatedCompletedZetaNormalizedZeroSide
        system zeroWindow cutoff f =
      guinandWeilTruncatedZeroSide system zeroWindow cutoff f := by
  classical
  unfold guinandWeilTruncatedCompletedZetaNormalizedZeroSide
  unfold guinandWeilTruncatedZeroSide
  apply Finset.sum_congr rfl
  intro rho _hrho
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · simp [completedZetaNormalizedZeroWeight, htrivial,
      htrivial_weight rho htrivial]
  · simp [completedZetaNormalizedZeroWeight, htrivial]

/--
If the raw project weight already vanishes on project-known trivial zeroes,
then the raw and completed-zeta normalized limiting zero sides agree.
-/
theorem guinandWeilCompletedZetaNormalizedZeroSide_eq_zeroSide_of_trivialWeight_eq_zero
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction)
    (htrivial_weight :
      forall rho : ZetaZeroSubtype,
        IsTrivialZetaZero (rho : Complex) -> system.weight f rho = 0) :
    guinandWeilCompletedZetaNormalizedZeroSide system f =
      guinandWeilZeroSide system f := by
  unfold guinandWeilCompletedZetaNormalizedZeroSide
  unfold guinandWeilZeroSide
  apply tsum_congr
  intro rho
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · simp [completedZetaNormalizedZeroWeight, htrivial,
      htrivial_weight rho htrivial]
  · simp [completedZetaNormalizedZeroWeight, htrivial]

/--
The contribution of one prime power in the symmetric completed-zeta
normalization.
-/
def guinandWeilPrimeTerm
    (f : SchwartzLineTestFunction)
    (n : Nat) : Real :=
  - (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
    (((SchwartzLineTestFunction.fourier f) (Real.log (n : Real))).re +
      ((SchwartzLineTestFunction.fourier f) (-Real.log (n : Real))).re)

/--
The compact-support source condition on the Fourier transform that makes the
concrete prime side finite.  This is the Paley-Wiener-style source-class
summability hypothesis in the completed-zeta normalization: outside a real
compact interval, both sampled values `F(log n)` and `F(-log n)` vanish.
-/
def GuinandWeilFourierCompactSupport
    (f : SchwartzLineTestFunction) : Prop :=
  ∃ R : Real, 0 <= R ∧
    ∀ x : Real, R < |x| -> SchwartzLineTestFunction.fourier f x = 0

/-- The truncated prime side, with prime powers cut off by `n <= cutoff`. -/
def guinandWeilTruncatedPrimeSide
    (cutoff : Nat)
    (f : SchwartzLineTestFunction) : Real :=
  (Finset.Icc 1 cutoff).sum (fun n : Nat => guinandWeilPrimeTerm f n)

/-- The limiting prime side attached to the concrete von-Mangoldt component. -/
def guinandWeilPrimeSide
    (f : SchwartzLineTestFunction) : Real :=
  ∑' n : Nat, guinandWeilPrimeTerm f n

/--
The completed-zeta pole side at `s = 0` and `s = 1`, transported to the
Riemann-Weil zero argument.
-/
def guinandWeilPoleSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) : Real :=
  (system.extension f (riemannWeilZeroArgument 0) +
    system.extension f (riemannWeilZeroArgument 1)).re

/-- The pole side is independent of the cutoff. -/
def guinandWeilTruncatedPoleSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (_cutoff : Nat)
    (f : SchwartzLineTestFunction) : Real :=
  guinandWeilPoleSide system f

/-- The logarithmic derivative of the completed-zeta Archimedean factor. -/
def guinandWeilGammaLogDerivative (t : Real) : Complex :=
  deriv Complex.Gammaℝ (criticalLinePoint t) / Complex.Gammaℝ (criticalLinePoint t)

/--
The real gamma side in the symmetric completed-zeta normalization.

This is kept as the raw Bochner integral expression; integrability and
continuity estimates are separate analytic obligations.
-/
def guinandWeilGammaSide
    (f : SchwartzLineTestFunction) : Real :=
  - (1 / (2 * Real.pi)) *
    ∫ t : Real, ((f t) * guinandWeilGammaLogDerivative t).re ∂volume

/-- The gamma side is independent of the cutoff. -/
def guinandWeilTruncatedGammaSide
    (_cutoff : Nat)
    (f : SchwartzLineTestFunction) : Real :=
  guinandWeilGammaSide f

/-- The assembled concrete finite-cutoff residual side. -/
def guinandWeilTruncatedResidualSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (cutoff : Nat)
    (f : SchwartzLineTestFunction) : Real :=
  guinandWeilTruncatedPrimeSide cutoff f +
    guinandWeilTruncatedPoleSide system cutoff f +
      guinandWeilTruncatedGammaSide cutoff f

/-- The limiting residual side assembled from the concrete prime, pole, and gamma sides. -/
def guinandWeilResidualSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) : Real :=
  guinandWeilPrimeSide f + guinandWeilPoleSide system f + guinandWeilGammaSide f

/-!
## Concrete source-to-project normalization

This is the Lean-native normalization bridge for the completed-zeta
Guinand-Weil convention used in this file.  The source theorem boundary remains
visible as the hypothesis `hformula`; the lemmas below prove that the source
zero/prime/pole/gamma notation is exactly the concrete project notation.
-/

/-- Source-side limiting data in the completed-zeta Guinand-Weil normalization. -/
def guinandWeilConcreteSourceSideData
    (system : SchwartzRiemannWeilExtensionSystem) :
    GuinandWeilFormulaSideData where
  sourceZeroSide := guinandWeilZeroSide system
  sourcePrimeSide := guinandWeilPrimeSide
  sourcePoleSide := guinandWeilPoleSide system
  sourceGammaSide := guinandWeilGammaSide

/-- Project-side limiting prime, pole, and gamma data for the same concrete normalization. -/
def guinandWeilConcreteProjectSideData
    (system : SchwartzRiemannWeilExtensionSystem) :
    SchwartzRiemannWeilFormulaSideData where
  primeSide := guinandWeilPrimeSide
  poleSide := guinandWeilPoleSide system
  gammaSide := guinandWeilGammaSide

/--
Source-side limiting data in the completed-zeta normalized zero-side
convention.  The prime, pole, and gamma sides stay in the concrete
completed-zeta normalization; only the zero side removes project-known trivial
zeroes.
-/
def guinandWeilCompletedZetaNormalizedSourceSideData
    (system : SchwartzRiemannWeilExtensionSystem) :
    GuinandWeilFormulaSideData where
  sourceZeroSide := guinandWeilCompletedZetaNormalizedZeroSide system
  sourcePrimeSide := guinandWeilPrimeSide
  sourcePoleSide := guinandWeilPoleSide system
  sourceGammaSide := guinandWeilGammaSide

/-- The concrete source residual side is the assembled concrete residual side. -/
@[simp]
theorem guinandWeilConcreteSourceSideData_sourceResidualSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    (guinandWeilConcreteSourceSideData system).sourceResidualSide f =
      guinandWeilResidualSide system f := by
  rfl

/-- The concrete project residual side is the assembled concrete residual side. -/
@[simp]
theorem guinandWeilConcreteProjectSideData_residualSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    (guinandWeilConcreteProjectSideData system).residualSide f =
      guinandWeilResidualSide system f := by
  rfl

/-- The completed-zeta normalized source residual side is still the concrete residual side. -/
@[simp]
theorem guinandWeilCompletedZetaNormalizedSourceSideData_sourceResidualSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    (guinandWeilCompletedZetaNormalizedSourceSideData system).sourceResidualSide f =
      guinandWeilResidualSide system f := by
  rfl

/--
The zero side induced by the extension-system summability certificate is
definitionally the concrete `system.weight` zero-side `tsum`.
-/
@[simp]
theorem guinandWeilConcrete_toZeroSide_zeroSide_eq
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction, Summable (system.weight f))
    (f : SchwartzLineTestFunction) :
    (system.toZeroSide hsummable).zeroSide f = guinandWeilZeroSide system f := by
  rfl

/--
The completed-zeta normalized zero side induced by the extension system is
definitionally the concrete normalized zero-side `tsum`.
-/
@[simp]
theorem guinandWeilCompletedZetaNormalized_toZeroSide_zeroSide_eq
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction,
        Summable (completedZetaNormalizedZeroWeight system f))
    (f : SchwartzLineTestFunction) :
    (system.toCompletedZetaNormalizedZeroSide hsummable).zeroSide f =
      guinandWeilCompletedZetaNormalizedZeroSide system f := by
  rfl

/-- The project prime side is the concrete source prime side. -/
@[simp]
theorem guinandWeilConcreteProject_primeSide_eq_sourcePrimeSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    (guinandWeilConcreteProjectSideData system).primeSide f =
      (guinandWeilConcreteSourceSideData system).sourcePrimeSide f := by
  rfl

/-- The project pole side is the concrete source pole side. -/
@[simp]
theorem guinandWeilConcreteProject_poleSide_eq_sourcePoleSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    (guinandWeilConcreteProjectSideData system).poleSide f =
      (guinandWeilConcreteSourceSideData system).sourcePoleSide f := by
  rfl

/-- The project gamma side is the concrete source gamma side. -/
@[simp]
theorem guinandWeilConcreteProject_gammaSide_eq_sourceGammaSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (f : SchwartzLineTestFunction) :
    (guinandWeilConcreteProjectSideData system).gammaSide f =
      (guinandWeilConcreteSourceSideData system).sourceGammaSide f := by
  rfl

/-- Source formula identity data for a supplied concrete Guinand-Weil source theorem. -/
def guinandWeilConcreteSourceFormulaData
    (system : SchwartzRiemannWeilExtensionSystem)
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilZeroSide system f = guinandWeilResidualSide system f) :
    GuinandWeilFormulaIdentityData where
  sideData := guinandWeilConcreteSourceSideData system
  sourceExplicitFormula := fun f => by
    change guinandWeilZeroSide system f =
      (guinandWeilConcreteSourceSideData system).sourceResidualSide f
    rw [guinandWeilConcreteSourceSideData_sourceResidualSide]
    exact hformula f

/--
The concrete componentwise normalization bridge from source Guinand-Weil sides
to the project zero/prime/pole/gamma sides.
-/
def guinandWeilConcreteComponentwiseNormalizationBridge
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction, Summable (system.weight f))
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilZeroSide system f = guinandWeilResidualSide system f) :
    GuinandWeilComponentwiseNormalizationBridge
      (guinandWeilConcreteSourceFormulaData system hformula)
      (system.toZeroSide hsummable) where
  sideData := guinandWeilConcreteProjectSideData system
  zeroSide_eq_sourceZeroSide := by
    intro f
    exact guinandWeilConcrete_toZeroSide_zeroSide_eq system hsummable f
  primeSide_eq_sourcePrimeSide := by
    intro f
    exact guinandWeilConcreteProject_primeSide_eq_sourcePrimeSide system f
  poleSide_eq_sourcePoleSide := by
    intro f
    exact guinandWeilConcreteProject_poleSide_eq_sourcePoleSide system f
  gammaSide_eq_sourceGammaSide := by
    intro f
    exact guinandWeilConcreteProject_gammaSide_eq_sourceGammaSide system f

/-- The project formula identity data produced by concrete componentwise normalization. -/
def guinandWeilConcreteFormulaData
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction, Summable (system.weight f))
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilZeroSide system f = guinandWeilResidualSide system f) :
    SchwartzRiemannWeilFormulaIdentityData (system.toZeroSide hsummable) :=
  GuinandWeilComponentwiseNormalizationBridge.toFormulaIdentityData
    (guinandWeilConcreteComponentwiseNormalizationBridge system hsummable hformula)

/--
After concrete componentwise normalization, the packaged project side data is
the concrete prime/pole/gamma data.
-/
@[simp]
theorem guinandWeilConcreteComponentwiseNormalizationBridge_sideData
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction, Summable (system.weight f))
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilZeroSide system f = guinandWeilResidualSide system f) :
    (guinandWeilConcreteFormulaData system hsummable hformula).sideData =
      guinandWeilConcreteProjectSideData system := by
  rfl

/-- The normalized project formula uses the concrete limiting prime side. -/
@[simp]
theorem guinandWeilConcreteFormulaData_primeSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction, Summable (system.weight f))
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilZeroSide system f = guinandWeilResidualSide system f)
    (f : SchwartzLineTestFunction) :
    (guinandWeilConcreteFormulaData system hsummable hformula).sideData.primeSide f =
      guinandWeilPrimeSide f := by
  rfl

/-- The normalized project formula uses the concrete limiting pole side. -/
@[simp]
theorem guinandWeilConcreteFormulaData_poleSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction, Summable (system.weight f))
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilZeroSide system f = guinandWeilResidualSide system f)
    (f : SchwartzLineTestFunction) :
    (guinandWeilConcreteFormulaData system hsummable hformula).sideData.poleSide f =
      guinandWeilPoleSide system f := by
  rfl

/-- The normalized project formula uses the concrete limiting gamma side. -/
@[simp]
theorem guinandWeilConcreteFormulaData_gammaSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction, Summable (system.weight f))
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilZeroSide system f = guinandWeilResidualSide system f)
    (f : SchwartzLineTestFunction) :
    (guinandWeilConcreteFormulaData system hsummable hformula).sideData.gammaSide f =
      guinandWeilGammaSide f := by
  rfl

/-- The normalized project formula uses the concrete limiting residual side. -/
@[simp]
theorem guinandWeilConcreteFormulaData_residualSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction, Summable (system.weight f))
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilZeroSide system f = guinandWeilResidualSide system f)
    (f : SchwartzLineTestFunction) :
    (guinandWeilConcreteFormulaData system hsummable hformula).sideData.residualSide f =
      guinandWeilResidualSide system f := by
  rfl

/--
The source theorem, after concrete componentwise normalization, is exactly the
project formula identity with the concrete residual side.
-/
theorem guinandWeilConcreteComponentwiseNormalization_explicitFormula
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction, Summable (system.weight f))
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilZeroSide system f = guinandWeilResidualSide system f)
    (f : SchwartzLineTestFunction) :
    (system.toZeroSide hsummable).zeroSide f =
      guinandWeilResidualSide system f := by
  simpa using
    (guinandWeilConcreteFormulaData system hsummable hformula).explicitFormula f

/--
Source formula identity data for a completed-zeta source theorem whose zero
side has already moved project-known trivial zeroes into the completed-zeta
normalization.
-/
def guinandWeilCompletedZetaNormalizedSourceFormulaData
    (system : SchwartzRiemannWeilExtensionSystem)
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilCompletedZetaNormalizedZeroSide system f =
          guinandWeilResidualSide system f) :
    GuinandWeilFormulaIdentityData where
  sideData := guinandWeilCompletedZetaNormalizedSourceSideData system
  sourceExplicitFormula := fun f => by
    change guinandWeilCompletedZetaNormalizedZeroSide system f =
      (guinandWeilCompletedZetaNormalizedSourceSideData system).sourceResidualSide f
    rw [guinandWeilCompletedZetaNormalizedSourceSideData_sourceResidualSide]
    exact hformula f

/--
Componentwise normalization bridge for the completed-zeta normalized zero side.

This is the concrete Guinand-Weil receiving surface for the course correction:
the source theorem supplies a nontrivial-zero-side identity, while the project
zero-side interface is built from `completedZetaNormalizedZeroWeight`.
-/
def guinandWeilCompletedZetaNormalizedComponentwiseNormalizationBridge
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction,
        Summable (completedZetaNormalizedZeroWeight system f))
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilCompletedZetaNormalizedZeroSide system f =
          guinandWeilResidualSide system f) :
    GuinandWeilComponentwiseNormalizationBridge
      (guinandWeilCompletedZetaNormalizedSourceFormulaData system hformula)
      (system.toCompletedZetaNormalizedZeroSide hsummable) where
  sideData := guinandWeilConcreteProjectSideData system
  zeroSide_eq_sourceZeroSide := by
    intro f
    exact guinandWeilCompletedZetaNormalized_toZeroSide_zeroSide_eq
      system hsummable f
  primeSide_eq_sourcePrimeSide := by
    intro f
    rfl
  poleSide_eq_sourcePoleSide := by
    intro f
    rfl
  gammaSide_eq_sourceGammaSide := by
    intro f
    rfl

/-- The project formula identity data produced by normalized componentwise normalization. -/
def guinandWeilCompletedZetaNormalizedFormulaData
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction,
        Summable (completedZetaNormalizedZeroWeight system f))
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilCompletedZetaNormalizedZeroSide system f =
          guinandWeilResidualSide system f) :
    SchwartzRiemannWeilFormulaIdentityData
      (system.toCompletedZetaNormalizedZeroSide hsummable) :=
  GuinandWeilComponentwiseNormalizationBridge.toFormulaIdentityData
    (guinandWeilCompletedZetaNormalizedComponentwiseNormalizationBridge
      system hsummable hformula)

/--
After completed-zeta normalized componentwise normalization, the packaged
project side data is the concrete prime/pole/gamma data.
-/
@[simp]
theorem guinandWeilCompletedZetaNormalizedComponentwiseNormalizationBridge_sideData
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction,
        Summable (completedZetaNormalizedZeroWeight system f))
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilCompletedZetaNormalizedZeroSide system f =
          guinandWeilResidualSide system f) :
    (guinandWeilCompletedZetaNormalizedFormulaData
      system hsummable hformula).sideData =
      guinandWeilConcreteProjectSideData system := by
  rfl

/--
The completed-zeta normalized source theorem becomes the project formula
identity with the concrete residual side.
-/
theorem guinandWeilCompletedZetaNormalizedComponentwiseNormalization_explicitFormula
    (system : SchwartzRiemannWeilExtensionSystem)
    (hsummable :
      forall f : SchwartzLineTestFunction,
        Summable (completedZetaNormalizedZeroWeight system f))
    (hformula :
      forall f : SchwartzLineTestFunction,
        guinandWeilCompletedZetaNormalizedZeroSide system f =
          guinandWeilResidualSide system f)
    (f : SchwartzLineTestFunction) :
    (system.toCompletedZetaNormalizedZeroSide hsummable).zeroSide f =
      guinandWeilResidualSide system f := by
  simpa using
    (guinandWeilCompletedZetaNormalizedFormulaData
      system hsummable hformula).explicitFormula f

/--
The finite-cutoff identity target for the concrete Guinand-Weil sides.

The next analytic proof obligation is to prove this proposition, or its
signed-error variant below, from the completed-zeta contour shift.
-/
def GuinandWeilConcreteFiniteCutoffIdentity
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (cutoff : Nat) : Prop :=
  forall f : SchwartzLineTestFunction,
    guinandWeilTruncatedZeroSide system zeroWindow cutoff f =
      guinandWeilTruncatedResidualSide system cutoff f

/--
Signed-error finite-cutoff identity target for contour-shift proofs.

Most published truncations produce an explicit error term first; vanishing or
bounded-error routes can then feed the existing limit packages.
-/
def GuinandWeilConcreteFiniteCutoffIdentityWithError
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (cutoff : Nat) : Prop :=
  forall f : SchwartzLineTestFunction,
    guinandWeilTruncatedZeroSide system zeroWindow cutoff f =
      guinandWeilTruncatedResidualSide system cutoff f + errorSide cutoff f

/-- The formula error attached to the concrete cutoff sides. -/
def guinandWeilConcreteFormulaError
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (cutoff : Nat)
    (f : SchwartzLineTestFunction) : Real :=
  guinandWeilTruncatedZeroSide system zeroWindow cutoff f -
    guinandWeilTruncatedResidualSide system cutoff f

/--
Completed-zeta normalized signed-error finite-cutoff identity target.

This is the source-formula target for the course-corrected normalization: the
finite zero side already omits project-known trivial zero contributions.
-/
def GuinandWeilCompletedZetaNormalizedFiniteCutoffIdentityWithError
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (errorSide : Nat -> SchwartzLineTestFunction -> Real)
    (cutoff : Nat) : Prop :=
  forall f : SchwartzLineTestFunction,
    guinandWeilTruncatedCompletedZetaNormalizedZeroSide
        system zeroWindow cutoff f =
      guinandWeilTruncatedResidualSide system cutoff f + errorSide cutoff f

/-- The completed-zeta normalized formula error attached to the cutoff sides. -/
def guinandWeilCompletedZetaNormalizedFormulaError
    (system : SchwartzRiemannWeilExtensionSystem)
    (zeroWindow : GuinandWeilZeroWindow)
    (cutoff : Nat)
    (f : SchwartzLineTestFunction) : Real :=
  guinandWeilTruncatedCompletedZetaNormalizedZeroSide
      system zeroWindow cutoff f -
    guinandWeilTruncatedResidualSide system cutoff f

end

end RiemannHypothesisProject
