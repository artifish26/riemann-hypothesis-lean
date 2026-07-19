import RiemannHypothesisProject.LocalRH

/-!
# Langlands-style purity bridge

This file records a small checked abstraction inspired by the function-field
and Langlands picture.

It does not formalize the Langlands program and does not assert that zeta has
such a model. It isolates the one feature that would be decisive for RH in this
project: a pure or unitary parameter whose unitarized phase gives a real height
for each relevant zero.

Once such real phase heights are supplied, the result is exactly the existing
real-spectrum bridge.
-/

namespace RiemannHypothesisProject

/--
A local purity/phase model for a chosen family of nontrivial zeta zeroes.

The intended analogy is: after the correct normalization, a pure Frobenius or
unitary automorphic parameter has a real phase. If zeroes in a chosen family are
realized by those real phases as `1 / 2 + i * t`, then local RH follows.
-/
structure LocalPurityPhaseModel (family : Complex -> Prop) where
  Parameter : Type
  phaseHeight : Parameter -> Real
  realizes_family_zeroes :
    forall s : Complex, family s -> IsNontrivialZetaZero s ->
      exists x : Parameter, criticalLinePoint (phaseHeight x) = s

namespace LocalPurityPhaseModel

/-- A local purity/phase model is a local real-spectrum model. -/
noncomputable def toLocalRealSpectrumModel
    {family : Complex -> Prop}
    (model : LocalPurityPhaseModel family) :
    LocalRealSpectrumModel family where
  Carrier := model.Parameter
  height := model.phaseHeight
  realizes_family_zeroes := model.realizes_family_zeroes

/-- Any local real-spectrum model may be viewed as a local purity/phase model. -/
noncomputable def ofLocalRealSpectrumModel
    {family : Complex -> Prop}
    (model : LocalRealSpectrumModel family) :
    LocalPurityPhaseModel family where
  Parameter := model.Carrier
  phaseHeight := model.height
  realizes_family_zeroes := model.realizes_family_zeroes

end LocalPurityPhaseModel

/-- A local purity/phase model proves RH on its family. -/
theorem RHOn.of_localPurityPhaseModel
    {family : Complex -> Prop}
    (model : LocalPurityPhaseModel family) :
    RHOn family :=
  RHOn.of_localRealSpectrumModel model.toLocalRealSpectrumModel

/--
A global purity/phase model for all nontrivial zeta zeroes.

This is the number-field analogue one would hope to extract from a much deeper
cohomological, spectral, or Langlands-style construction: every nontrivial zero
is represented by a real unitarized phase height.
-/
structure PurityPhaseModel where
  Parameter : Type
  phaseHeight : Parameter -> Real
  realizes_nontrivial_zeroes :
    forall s : Complex, IsNontrivialZetaZero s ->
      exists x : Parameter, criticalLinePoint (phaseHeight x) = s

namespace PurityPhaseModel

/-- A global purity/phase model is a global real-spectrum model. -/
noncomputable def toRealSpectrumModel
    (model : PurityPhaseModel) :
    RealSpectrumModel where
  Carrier := model.Parameter
  height := model.phaseHeight
  realizes_nontrivial_zeroes := model.realizes_nontrivial_zeroes

/-- A global purity/phase model gives a local model for the universal family. -/
noncomputable def toLocalPurityPhaseModel
    (model : PurityPhaseModel) :
    LocalPurityPhaseModel (fun _ : Complex => True) where
  Parameter := model.Parameter
  phaseHeight := model.phaseHeight
  realizes_family_zeroes := fun s _ hs =>
    model.realizes_nontrivial_zeroes s hs

/-- Any global real-spectrum model may be viewed as a global purity model. -/
noncomputable def ofRealSpectrumModel
    (model : RealSpectrumModel) :
    PurityPhaseModel where
  Parameter := model.Carrier
  phaseHeight := model.height
  realizes_nontrivial_zeroes := model.realizes_nontrivial_zeroes

end PurityPhaseModel

/-- A global purity/phase model proves the project-local RH statement. -/
theorem RHStatement.of_purityPhaseModel
    (model : PurityPhaseModel) :
    RHStatement :=
  RHStatement.of_realSpectrumModel model.toRealSpectrumModel

/-- A global purity/phase model proves Mathlib's `RiemannHypothesis`. -/
theorem mathlib_RH_of_purityPhaseModel
    (model : PurityPhaseModel) :
    RiemannHypothesis :=
  mathlib_RH_of_realSpectrumModel model.toRealSpectrumModel

end RiemannHypothesisProject
