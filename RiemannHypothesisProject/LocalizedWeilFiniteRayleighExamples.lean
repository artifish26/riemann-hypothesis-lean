import RiemannHypothesisProject.LocalizedWeilQuadraticFormTarget

/-!
# Localized finite Rayleigh examples

This file mirrors the numerical validation workbench with a tiny checked Lean
case: a one-dimensional finite Rayleigh matrix with nonnegative weight.  It is
not a zeta theorem.  Its purpose is to keep the finite-matrix validation route
connected to the support-restricted residual-positivity API.
-/

namespace RiemannHypothesisProject

open scoped BigOperators

/--
One-dimensional finite Rayleigh data with kernel `[weight]`.

The positivity certificate is the elementary inequality
`0 <= weight * x ^ 2`, assuming `0 <= weight`.
-/
noncomputable def oneByOneRayleighData
    (coordinate : SchwartzLineTestFunction -> Real)
    (weight : Real)
    (weight_nonneg : 0 <= weight) :
    LocalizedWeilFiniteRayleighData Unit where
  coordinate := fun f _ => coordinate f
  kernel := fun _ _ => weight
  quadratic_nonneg := by
    intro x
    have hx : 0 <= (x ()) ^ 2 := sq_nonneg (x ())
    have hprod : 0 <= weight * (x ()) ^ 2 := mul_nonneg weight_nonneg hx
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hprod

/-- The one-dimensional Rayleigh quadratic form is `weight * coordinate f ^ 2`. -/
theorem oneByOneRayleighData_quadraticForm
    (coordinate : SchwartzLineTestFunction -> Real)
    (weight : Real)
    (weight_nonneg : 0 <= weight)
    (f : SchwartzLineTestFunction) :
    (oneByOneRayleighData coordinate weight weight_nonneg).quadraticForm f =
      weight * (coordinate f) ^ 2 := by
  simp [oneByOneRayleighData, LocalizedWeilFiniteRayleighData.quadraticForm,
    pow_two, mul_comm, mul_left_comm]

/--
Build a localized finite-Rayleigh target from a one-dimensional positive matrix.

The only analytic input is the residual-identification equation on the chosen
admissible class.
-/
noncomputable def oneByOneRayleighTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (coordinate : SchwartzLineTestFunction -> Real)
    (weight : Real)
    (weight_nonneg : 0 <= weight)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          weight * (coordinate f) ^ 2 = formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFiniteRayleighTarget formulaData Unit where
  admissible := admissible
  rayleighData := oneByOneRayleighData coordinate weight weight_nonneg
  rayleighQuadratic_eq_residualSide_on_admissible := by
    intro f hf
    calc
      (oneByOneRayleighData coordinate weight weight_nonneg).quadraticForm f =
          weight * (coordinate f) ^ 2 :=
        oneByOneRayleighData_quadraticForm coordinate weight weight_nonneg f
      _ = formulaData.sideData.residualSide f :=
        rayleigh_eq_residualSide_on_admissible f hf
  restricted_positivity_implies_RHOn_univ :=
    restricted_positivity_implies_RHOn_univ

/--
The one-dimensional positive Rayleigh matrix gives support-restricted residual
positivity after residual identification.
-/
noncomputable def oneByOneRayleighSupportRestrictedFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (coordinate : SchwartzLineTestFunction -> Real)
    (weight : Real)
    (weight_nonneg : 0 <= weight)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          weight * (coordinate f) ^ 2 = formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True)) :
    SupportRestrictedFormulaResidualPositivityData formulaData :=
  (oneByOneRayleighTarget
    coordinate
    weight
    weight_nonneg
    admissible
    rayleigh_eq_residualSide_on_admissible
    restricted_positivity_implies_RHOn_univ)
    |>.toSupportRestrictedFormulaResidualPositivityData

/--
Pointwise residual nonnegativity obtained from the one-dimensional positive
Rayleigh matrix.
-/
theorem oneByOneRayleigh_residual_nonneg_on_admissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (coordinate : SchwartzLineTestFunction -> Real)
    (weight : Real)
    (weight_nonneg : 0 <= weight)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          weight * (coordinate f) ^ 2 = formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True))
    (f : SchwartzLineTestFunction)
    (hf : admissible f) :
    0 <= formulaData.sideData.residualSide f :=
  (oneByOneRayleighSupportRestrictedFormulaResidualPositivityData
    coordinate
    weight
    weight_nonneg
    admissible
    rayleigh_eq_residualSide_on_admissible
    restricted_positivity_implies_RHOn_univ)
    |>.residual_nonneg_on_admissible f hf

/--
The quadratic form for a diagonal finite Rayleigh kernel.

This is the finite-dimensional calculation behind diagonal positive matrix
checks: all off-diagonal terms vanish, leaving a weighted sum of squares.
-/
theorem diagonalRayleighKernel_quadratic
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (weight : Index -> Real)
    (x : Index -> Real) :
    (∑ i : Index, ∑ j : Index, x i * (if i = j then weight i else 0) * x j) =
      ∑ i : Index, weight i * (x i) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _hi
  calc
    (∑ j : Index, x i * (if i = j then weight i else 0) * x j) =
        x i * weight i * x i := by
      rw [Finset.sum_eq_single i]
      · simp [mul_comm, mul_left_comm]
      · intro j _hj hji
        have hij : i ≠ j := by
          intro h
          exact hji h.symm
        simp [hij]
      · intro hi
        simp at hi
    _ = weight i * (x i) ^ 2 := by
      simp [pow_two, mul_comm, mul_left_comm]

/--
Finite Rayleigh data for any diagonal kernel with nonnegative diagonal weights.
-/
noncomputable def diagonalRayleighData
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coordinate : SchwartzLineTestFunction -> Index -> Real)
    (weight : Index -> Real)
    (weight_nonneg : forall i : Index, 0 <= weight i) :
    LocalizedWeilFiniteRayleighData Index where
  coordinate := coordinate
  kernel := fun i j => if i = j then weight i else 0
  quadratic_nonneg := by
    intro x
    rw [diagonalRayleighKernel_quadratic weight x]
    exact Finset.sum_nonneg fun i _hi =>
      mul_nonneg (weight_nonneg i) (sq_nonneg (x i))

/-- The diagonal Rayleigh quadratic form is a weighted sum of coordinate squares. -/
theorem diagonalRayleighData_quadraticForm
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coordinate : SchwartzLineTestFunction -> Index -> Real)
    (weight : Index -> Real)
    (weight_nonneg : forall i : Index, 0 <= weight i)
    (f : SchwartzLineTestFunction) :
    (diagonalRayleighData coordinate weight weight_nonneg).quadraticForm f =
      ∑ i : Index, weight i * (coordinate f i) ^ 2 := by
  change
    (∑ i : Index, ∑ j : Index,
      coordinate f i * (if i = j then weight i else 0) * coordinate f j) =
      ∑ i : Index, weight i * (coordinate f i) ^ 2
  exact diagonalRayleighKernel_quadratic weight (coordinate f)

/--
Build a localized finite-Rayleigh target from a diagonal positive matrix.

The analytic obligation is exactly the final equality: the weighted finite
Rayleigh quadratic form must be identified with the formula residual on the
admissible class.
-/
noncomputable def diagonalRayleighTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coordinate : SchwartzLineTestFunction -> Index -> Real)
    (weight : Index -> Real)
    (weight_nonneg : forall i : Index, 0 <= weight i)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          (∑ i : Index, weight i * (coordinate f i) ^ 2) =
            formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFiniteRayleighTarget formulaData Index where
  admissible := admissible
  rayleighData := diagonalRayleighData coordinate weight weight_nonneg
  rayleighQuadratic_eq_residualSide_on_admissible := by
    intro f hf
    calc
      (diagonalRayleighData coordinate weight weight_nonneg).quadraticForm f =
          ∑ i : Index, weight i * (coordinate f i) ^ 2 :=
        diagonalRayleighData_quadraticForm coordinate weight weight_nonneg f
      _ = formulaData.sideData.residualSide f :=
        rayleigh_eq_residualSide_on_admissible f hf
  restricted_positivity_implies_RHOn_univ :=
    restricted_positivity_implies_RHOn_univ

/--
A diagonal positive finite Rayleigh matrix gives support-restricted residual
positivity once residual identification is supplied.
-/
noncomputable def diagonalRayleighSupportRestrictedFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coordinate : SchwartzLineTestFunction -> Index -> Real)
    (weight : Index -> Real)
    (weight_nonneg : forall i : Index, 0 <= weight i)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          (∑ i : Index, weight i * (coordinate f i) ^ 2) =
            formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True)) :
    SupportRestrictedFormulaResidualPositivityData formulaData :=
  (diagonalRayleighTarget
    coordinate
    weight
    weight_nonneg
    admissible
    rayleigh_eq_residualSide_on_admissible
    restricted_positivity_implies_RHOn_univ)
    |>.toSupportRestrictedFormulaResidualPositivityData

/--
Pointwise residual nonnegativity obtained from a diagonal positive finite
Rayleigh matrix.
-/
theorem diagonalRayleigh_residual_nonneg_on_admissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coordinate : SchwartzLineTestFunction -> Index -> Real)
    (weight : Index -> Real)
    (weight_nonneg : forall i : Index, 0 <= weight i)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          (∑ i : Index, weight i * (coordinate f i) ^ 2) =
            formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True))
    (f : SchwartzLineTestFunction)
    (hf : admissible f) :
    0 <= formulaData.sideData.residualSide f :=
  (diagonalRayleighSupportRestrictedFormulaResidualPositivityData
    coordinate
    weight
    weight_nonneg
    admissible
    rayleigh_eq_residualSide_on_admissible
    restricted_positivity_implies_RHOn_univ)
    |>.residual_nonneg_on_admissible f hf

/--
Finite Rayleigh data from a Gram/Cholesky feature map.

The Rayleigh index is the feature index. The coordinate of a test function at a
feature is the finite pairing with that feature, so positivity is just a sum of
squares of feature pairings.
-/
noncomputable def finiteGramRayleighData
    {Index Feature : Type} [Fintype Index] [Fintype Feature] [DecidableEq Feature]
    (coordinate : SchwartzLineTestFunction -> Index -> Real)
    (feature : Feature -> Index -> Real) :
    LocalizedWeilFiniteRayleighData Feature :=
  diagonalRayleighData
    (fun f a => ∑ i : Index, feature a i * coordinate f i)
    (fun _ : Feature => 1)
    (fun _ => zero_le_one)

/--
The Gram/Cholesky finite Rayleigh quadratic form is the existing finite Gram
quadratic form on the encoded coordinates.
-/
theorem finiteGramRayleighData_quadraticForm
    {Index Feature : Type} [Fintype Index] [Fintype Feature] [DecidableEq Feature]
    (coordinate : SchwartzLineTestFunction -> Index -> Real)
    (feature : Feature -> Index -> Real)
    (f : SchwartzLineTestFunction) :
    (finiteGramRayleighData coordinate feature).quadraticForm f =
      finiteGramQuadraticForm feature (coordinate f) := by
  simp [finiteGramRayleighData, diagonalRayleighData_quadraticForm,
    finiteGramQuadraticForm]

/--
Build a localized finite-Rayleigh target from Gram/Cholesky feature data.

This is the checked Lean counterpart of a non-diagonal positive matrix supplied
by a factorization `K = A^T A`. The residual-identification equation remains
the analytic input.
-/
noncomputable def finiteGramRayleighTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index Feature : Type} [Fintype Index] [Fintype Feature] [DecidableEq Feature]
    (coordinate : SchwartzLineTestFunction -> Index -> Real)
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (coordinate f) =
            formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFiniteRayleighTarget formulaData Feature where
  admissible := admissible
  rayleighData := finiteGramRayleighData coordinate feature
  rayleighQuadratic_eq_residualSide_on_admissible := by
    intro f hf
    calc
      (finiteGramRayleighData coordinate feature).quadraticForm f =
          finiteGramQuadraticForm feature (coordinate f) :=
        finiteGramRayleighData_quadraticForm coordinate feature f
      _ = formulaData.sideData.residualSide f :=
        rayleigh_eq_residualSide_on_admissible f hf
  restricted_positivity_implies_RHOn_univ :=
    restricted_positivity_implies_RHOn_univ

/--
Gram/Cholesky finite Rayleigh data gives support-restricted residual positivity
once residual identification is supplied.
-/
noncomputable def finiteGramRayleighSupportRestrictedFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index Feature : Type} [Fintype Index] [Fintype Feature] [DecidableEq Feature]
    (coordinate : SchwartzLineTestFunction -> Index -> Real)
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (coordinate f) =
            formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True)) :
    SupportRestrictedFormulaResidualPositivityData formulaData :=
  (finiteGramRayleighTarget
    coordinate
    feature
    admissible
    rayleigh_eq_residualSide_on_admissible
    restricted_positivity_implies_RHOn_univ)
    |>.toSupportRestrictedFormulaResidualPositivityData

/--
Build the Gram/Cholesky finite Rayleigh target when the residual
identification is first proved in source residual notation.
-/
noncomputable def finiteGramRayleighSourceResidualTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index Feature : Type} [Fintype Index] [Fintype Feature] [DecidableEq Feature]
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coordinate : SchwartzLineTestFunction -> Index -> Real)
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (coordinate f) =
            sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFiniteRayleighTarget formulaData Feature :=
  LocalizedWeilFiniteRayleighTarget.ofSourceResidualSideEq
    sourceResidualSide
    residualSide_eq_source
    admissible
    (finiteGramRayleighData coordinate feature)
    (by
      intro f hf
      calc
        (finiteGramRayleighData coordinate feature).quadraticForm f =
            finiteGramQuadraticForm feature (coordinate f) :=
          finiteGramRayleighData_quadraticForm coordinate feature f
        _ = sourceResidualSide f :=
          rayleigh_eq_sourceResidualSide_on_admissible f hf)
    restricted_source_positivity_implies_RHOn_univ

/--
Source-residual finite Gram/Rayleigh data gives support-restricted residual
positivity after normalization to the formula residual side.
-/
noncomputable def finiteGramRayleighSourceResidualSupportRestrictedFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index Feature : Type} [Fintype Index] [Fintype Feature] [DecidableEq Feature]
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coordinate : SchwartzLineTestFunction -> Index -> Real)
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (coordinate f) =
            sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    SupportRestrictedFormulaResidualPositivityData formulaData :=
  (finiteGramRayleighSourceResidualTarget
    sourceResidualSide
    residualSide_eq_source
    coordinate
    feature
    admissible
    rayleigh_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ)
    |>.toSupportRestrictedFormulaResidualPositivityData

/--
Pointwise formula-residual nonnegativity obtained from a finite Gram/Rayleigh
identity stated in source residual notation.
-/
theorem finiteGramRayleigh_sourceResidual_residual_nonneg_on_admissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index Feature : Type} [Fintype Index] [Fintype Feature] [DecidableEq Feature]
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coordinate : SchwartzLineTestFunction -> Index -> Real)
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (coordinate f) =
            sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (f : SchwartzLineTestFunction)
    (hf : admissible f) :
    0 <= formulaData.sideData.residualSide f :=
  (finiteGramRayleighSourceResidualSupportRestrictedFormulaResidualPositivityData
    sourceResidualSide
    residualSide_eq_source
    coordinate
    feature
    admissible
    rayleigh_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ)
    |>.residual_nonneg_on_admissible f hf

/--
Pointwise residual nonnegativity obtained from Gram/Cholesky finite Rayleigh
data.
-/
theorem finiteGramRayleigh_residual_nonneg_on_admissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index Feature : Type} [Fintype Index] [Fintype Feature] [DecidableEq Feature]
    (coordinate : SchwartzLineTestFunction -> Index -> Real)
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (coordinate f) =
            formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True))
    (f : SchwartzLineTestFunction)
    (hf : admissible f) :
    0 <= formulaData.sideData.residualSide f :=
  (finiteGramRayleighSupportRestrictedFormulaResidualPositivityData
    coordinate
    feature
    admissible
    rayleigh_eq_residualSide_on_admissible
    restricted_positivity_implies_RHOn_univ)
    |>.residual_nonneg_on_admissible f hf

/--
The symmetric `2 x 2` kernel with diagonal entries `a`, `c` and off-diagonal
entry `b`.

This is the first compressed finite-matrix positivity target that does not ask
for a Gram/Cholesky factorization as input.
-/
def twoByTwoPrincipalMinorKernel (a b c : Real) (i j : Fin 2) : Real :=
  if i = 0 then
    if j = 0 then a else b
  else
    if j = 0 then b else c

/-- The Rayleigh quotient of the symmetric `2 x 2` kernel in coordinates. -/
theorem twoByTwoPrincipalMinorKernel_quadratic
    (a b c : Real)
    (x : Fin 2 -> Real) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      x i * twoByTwoPrincipalMinorKernel a b c i j * x j) =
      a * (x 0) ^ 2 + 2 * b * x 0 * x 1 + c * (x 1) ^ 2 := by
  simp [twoByTwoPrincipalMinorKernel, Fin.sum_univ_two, pow_two]
  ring

/--
The concrete `2 x 2` principal-minor positivity criterion.

For a symmetric matrix `[[a, b], [b, c]]`, the Rayleigh quotient is
nonnegative whenever the first pivot is positive and the determinant is
nonnegative.  This is a finite compressed positivity theorem, not an endpoint
adapter.
-/
theorem twoByTwoPrincipalMinorKernel_quadratic_nonneg
    (a b c : Real)
    (a_pos : 0 < a)
    (det_nonneg : 0 <= a * c - b ^ 2)
    (x : Fin 2 -> Real) :
    0 <= ∑ i : Fin 2, ∑ j : Fin 2,
      x i * twoByTwoPrincipalMinorKernel a b c i j * x j := by
  rw [twoByTwoPrincipalMinorKernel_quadratic]
  have a_nonneg : 0 <= a := le_of_lt a_pos
  have det_div_nonneg : 0 <= (a * c - b ^ 2) / a :=
    div_nonneg det_nonneg a_nonneg
  have complete_square :
      a * (x 0) ^ 2 + 2 * b * x 0 * x 1 + c * (x 1) ^ 2 =
        a * (x 0 + (b / a) * x 1) ^ 2 +
          ((a * c - b ^ 2) / a) * (x 1) ^ 2 := by
    field_simp [ne_of_gt a_pos]
    ring
  rw [complete_square]
  exact add_nonneg
    (mul_nonneg a_nonneg (sq_nonneg (x 0 + (b / a) * x 1)))
    (mul_nonneg det_div_nonneg (sq_nonneg (x 1)))

/--
Finite Rayleigh data from the direct `2 x 2` principal-minor criterion.
-/
noncomputable def twoByTwoPrincipalMinorRayleighData
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (a b c : Real)
    (a_pos : 0 < a)
    (det_nonneg : 0 <= a * c - b ^ 2) :
    LocalizedWeilFiniteRayleighData (Fin 2) where
  coordinate := coordinate
  kernel := twoByTwoPrincipalMinorKernel a b c
  quadratic_nonneg :=
    twoByTwoPrincipalMinorKernel_quadratic_nonneg a b c a_pos det_nonneg

/-- The direct principal-minor Rayleigh data has the expected quadratic form. -/
theorem twoByTwoPrincipalMinorRayleighData_quadraticForm
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (a b c : Real)
    (a_pos : 0 < a)
    (det_nonneg : 0 <= a * c - b ^ 2)
    (f : SchwartzLineTestFunction) :
    (twoByTwoPrincipalMinorRayleighData
      coordinate a b c a_pos det_nonneg).quadraticForm f =
      a * (coordinate f 0) ^ 2 +
        2 * b * coordinate f 0 * coordinate f 1 +
          c * (coordinate f 1) ^ 2 := by
  change
    (∑ i : Fin 2, ∑ j : Fin 2,
      coordinate f i * twoByTwoPrincipalMinorKernel a b c i j *
        coordinate f j) = _
  exact twoByTwoPrincipalMinorKernel_quadratic a b c (coordinate f)

/-- The coordinate vector `(x0, x1)` as a function on `Fin 2`. -/
def finTwoCoordinateVector (x0 x1 : Real) (i : Fin 2) : Real :=
  if i = 0 then x0 else x1

@[simp]
theorem finTwoCoordinateVector_zero (x0 x1 : Real) :
    finTwoCoordinateVector x0 x1 0 = x0 := by
  simp [finTwoCoordinateVector]

@[simp]
theorem finTwoCoordinateVector_one (x0 x1 : Real) :
    finTwoCoordinateVector x0 x1 1 = x1 := by
  simp [finTwoCoordinateVector]

/-- The first diagonal coefficient is the Rayleigh value on the first basis test. -/
theorem twoByTwoPrincipalMinorKernel_firstCoefficient
    (a b c : Real) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      finTwoCoordinateVector 1 0 i *
        twoByTwoPrincipalMinorKernel a b c i j *
          finTwoCoordinateVector 1 0 j) = a := by
  rw [twoByTwoPrincipalMinorKernel_quadratic]
  simp [finTwoCoordinateVector]

/-- The second diagonal coefficient is the Rayleigh value on the second basis test. -/
theorem twoByTwoPrincipalMinorKernel_secondCoefficient
    (a b c : Real) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      finTwoCoordinateVector 0 1 i *
        twoByTwoPrincipalMinorKernel a b c i j *
          finTwoCoordinateVector 0 1 j) = c := by
  rw [twoByTwoPrincipalMinorKernel_quadratic]
  simp [finTwoCoordinateVector]

/--
The off-diagonal coefficient is recovered by the usual polarization test
`Q(e0 + e1) - Q(e0) - Q(e1)`.
-/
theorem twoByTwoPrincipalMinorKernel_offDiagonalCoefficient
    (a b c : Real) :
    ((∑ i : Fin 2, ∑ j : Fin 2,
        finTwoCoordinateVector 1 1 i *
          twoByTwoPrincipalMinorKernel a b c i j *
            finTwoCoordinateVector 1 1 j) -
      (∑ i : Fin 2, ∑ j : Fin 2,
        finTwoCoordinateVector 1 0 i *
          twoByTwoPrincipalMinorKernel a b c i j *
            finTwoCoordinateVector 1 0 j) -
      (∑ i : Fin 2, ∑ j : Fin 2,
        finTwoCoordinateVector 0 1 i *
          twoByTwoPrincipalMinorKernel a b c i j *
            finTwoCoordinateVector 0 1 j)) / 2 = b := by
  rw [twoByTwoPrincipalMinorKernel_quadratic,
    twoByTwoPrincipalMinorKernel_firstCoefficient,
    twoByTwoPrincipalMinorKernel_secondCoefficient]
  simp [finTwoCoordinateVector]
  ring

/--
Admissible coefficient-test identity for the first diagonal coefficient of the
compressed `2 x 2` residual side.
-/
theorem twoByTwoPrincipalMinor_residual_firstCoefficient_on_admissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (a b c : Real)
    (a_pos : 0 < a)
    (det_nonneg : 0 <= a * c - b ^ 2)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          (twoByTwoPrincipalMinorRayleighData
            coordinate a b c a_pos det_nonneg).quadraticForm f =
            formulaData.sideData.residualSide f)
    (coefficientTest : SchwartzLineTestFunction)
    (coefficientTest_admissible : admissible coefficientTest)
    (coefficientTest_coordinates :
      coordinate coefficientTest = finTwoCoordinateVector 1 0) :
    formulaData.sideData.residualSide coefficientTest = a := by
  rw [← rayleigh_eq_residualSide_on_admissible
    coefficientTest coefficientTest_admissible]
  rw [twoByTwoPrincipalMinorRayleighData_quadraticForm]
  rw [coefficientTest_coordinates]
  simp [finTwoCoordinateVector]

/--
Admissible coefficient-test identity for the second diagonal coefficient of the
compressed `2 x 2` residual side.
-/
theorem twoByTwoPrincipalMinor_residual_secondCoefficient_on_admissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (a b c : Real)
    (a_pos : 0 < a)
    (det_nonneg : 0 <= a * c - b ^ 2)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          (twoByTwoPrincipalMinorRayleighData
            coordinate a b c a_pos det_nonneg).quadraticForm f =
            formulaData.sideData.residualSide f)
    (coefficientTest : SchwartzLineTestFunction)
    (coefficientTest_admissible : admissible coefficientTest)
    (coefficientTest_coordinates :
      coordinate coefficientTest = finTwoCoordinateVector 0 1) :
    formulaData.sideData.residualSide coefficientTest = c := by
  rw [← rayleigh_eq_residualSide_on_admissible
    coefficientTest coefficientTest_admissible]
  rw [twoByTwoPrincipalMinorRayleighData_quadraticForm]
  rw [coefficientTest_coordinates]
  simp [finTwoCoordinateVector]

/--
Admissible coefficient-test identity for the off-diagonal coefficient of the
compressed `2 x 2` residual side.

This is the finite Rayleigh analogue of a coefficient-test identity: once the
three tests realizing `e0`, `e1`, and `e0 + e1` are admissible and the local
Rayleigh form is identified with the residual side on them, the off-diagonal
coefficient is determined by residual values.
-/
theorem twoByTwoPrincipalMinor_residual_offDiagonalCoefficient_on_admissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (a b c : Real)
    (a_pos : 0 < a)
    (det_nonneg : 0 <= a * c - b ^ 2)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          (twoByTwoPrincipalMinorRayleighData
            coordinate a b c a_pos det_nonneg).quadraticForm f =
            formulaData.sideData.residualSide f)
    (firstTest secondTest sumTest : SchwartzLineTestFunction)
    (firstTest_admissible : admissible firstTest)
    (secondTest_admissible : admissible secondTest)
    (sumTest_admissible : admissible sumTest)
    (firstTest_coordinates : coordinate firstTest = finTwoCoordinateVector 1 0)
    (secondTest_coordinates : coordinate secondTest = finTwoCoordinateVector 0 1)
    (sumTest_coordinates : coordinate sumTest = finTwoCoordinateVector 1 1) :
    (formulaData.sideData.residualSide sumTest -
      formulaData.sideData.residualSide firstTest -
        formulaData.sideData.residualSide secondTest) / 2 = b := by
  have hfirst :
      formulaData.sideData.residualSide firstTest = a :=
    twoByTwoPrincipalMinor_residual_firstCoefficient_on_admissible
      coordinate a b c a_pos det_nonneg admissible
      rayleigh_eq_residualSide_on_admissible
      firstTest firstTest_admissible firstTest_coordinates
  have hsecond :
      formulaData.sideData.residualSide secondTest = c :=
    twoByTwoPrincipalMinor_residual_secondCoefficient_on_admissible
      coordinate a b c a_pos det_nonneg admissible
      rayleigh_eq_residualSide_on_admissible
      secondTest secondTest_admissible secondTest_coordinates
  have hsum :
      formulaData.sideData.residualSide sumTest = a + 2 * b + c := by
    rw [← rayleigh_eq_residualSide_on_admissible sumTest sumTest_admissible]
    rw [twoByTwoPrincipalMinorRayleighData_quadraticForm]
    rw [sumTest_coordinates]
    simp [finTwoCoordinateVector]
  rw [hsum, hfirst, hsecond]
  ring

/--
The concrete 2x2 feature map exported by
`validation_outputs/toy_gram_2x2_features.csv`.

Rows are features and columns are indices:

```text
1,1
0,1
```
-/
def exportedToyGramTwoByTwoFeature (feature index : Fin 2) : Real :=
  if feature = 0 then 1 else if index = 0 then 0 else 1

/--
The exported 2x2 feature map computes to the expected sum of two squares.
-/
theorem exportedToyGramTwoByTwoFeature_quadratic
    (x : Fin 2 -> Real) :
    finiteGramQuadraticForm exportedToyGramTwoByTwoFeature x =
      (x 0 + x 1) ^ 2 + (x 1) ^ 2 := by
  simp [finiteGramQuadraticForm, exportedToyGramTwoByTwoFeature,
    Fin.sum_univ_two]

/-- The exported 2x2 two-square form is nonnegative. -/
theorem exportedToyGramTwoByTwoSquares_nonneg
    (x : Fin 2 -> Real) :
    0 <= (x 0 + x 1) ^ 2 + (x 1) ^ 2 :=
  add_nonneg (sq_nonneg (x 0 + x 1)) (sq_nonneg (x 1))

/--
The exported 2x2 two-square form has trivial kernel.

This records the finite positive-definite part of the exported Gram fixture:
the only vector whose two feature pairings both vanish is the zero vector.
-/
theorem exportedToyGramTwoByTwoSquares_eq_zero_iff
    (x : Fin 2 -> Real) :
    (x 0 + x 1) ^ 2 + (x 1) ^ 2 = 0 <-> x 0 = 0 /\ x 1 = 0 := by
  constructor
  · intro h
    have hparts :
        (x 0 + x 1) ^ 2 = 0 /\ (x 1) ^ 2 = 0 :=
      (add_eq_zero_iff_of_nonneg
        (sq_nonneg (x 0 + x 1))
        (sq_nonneg (x 1))).mp h
    have hxsum : x 0 + x 1 = 0 := sq_eq_zero_iff.mp hparts.1
    have hx1 : x 1 = 0 := sq_eq_zero_iff.mp hparts.2
    have hx0 : x 0 = 0 := by
      simpa [hx1] using hxsum
    exact ⟨hx0, hx1⟩
  · rintro ⟨hx0, hx1⟩
    simp [hx0, hx1]

/--
The matrix kernel reconstructed from the exported 2x2 feature rows.

For the CSV feature matrix

```text
1,1
0,1
```

this is the Gram matrix `[[1, 1], [1, 2]]`.
-/
noncomputable def exportedToyGramTwoByTwoKernel (i j : Fin 2) : Real :=
  finiteGramKernel exportedToyGramTwoByTwoFeature i j

/-- The exported 2x2 feature rows reconstruct the expected Gram matrix entries. -/
theorem exportedToyGramTwoByTwoKernel_entries :
    exportedToyGramTwoByTwoKernel 0 0 = 1 ∧
    exportedToyGramTwoByTwoKernel 0 1 = 1 ∧
    exportedToyGramTwoByTwoKernel 1 0 = 1 ∧
    exportedToyGramTwoByTwoKernel 1 1 = 2 := by
  simp [exportedToyGramTwoByTwoKernel, finiteGramKernel,
    exportedToyGramTwoByTwoFeature]

/--
The Rayleigh quotient of the reconstructed exported 2x2 Gram matrix is the
same two-square form as the exported feature map.
-/
theorem exportedToyGramTwoByTwoKernel_quadratic
    (x : Fin 2 -> Real) :
    (∑ i, ∑ j, x i * exportedToyGramTwoByTwoKernel i j * x j) =
      (x 0 + x 1) ^ 2 + (x 1) ^ 2 := by
  calc
    (∑ i, ∑ j, x i * exportedToyGramTwoByTwoKernel i j * x j) =
        finiteGramQuadraticForm exportedToyGramTwoByTwoFeature x := by
      simpa [exportedToyGramTwoByTwoKernel] using
        finiteGramKernel_quadraticForm exportedToyGramTwoByTwoFeature x
    _ = (x 0 + x 1) ^ 2 + (x 1) ^ 2 :=
      exportedToyGramTwoByTwoFeature_quadratic x

/-- The reconstructed exported 2x2 Gram kernel is positive semidefinite. -/
theorem exportedToyGramTwoByTwoKernel_quadratic_nonneg
    (x : Fin 2 -> Real) :
    0 <= (∑ i, ∑ j, x i * exportedToyGramTwoByTwoKernel i j * x j) := by
  rw [exportedToyGramTwoByTwoKernel_quadratic]
  exact exportedToyGramTwoByTwoSquares_nonneg x

/-- The reconstructed exported 2x2 Gram kernel has trivial kernel. -/
theorem exportedToyGramTwoByTwoKernel_quadratic_eq_zero_iff
    (x : Fin 2 -> Real) :
    (∑ i, ∑ j, x i * exportedToyGramTwoByTwoKernel i j * x j) = 0 <->
      x 0 = 0 /\ x 1 = 0 := by
  rw [exportedToyGramTwoByTwoKernel_quadratic]
  exact exportedToyGramTwoByTwoSquares_eq_zero_iff x

/--
Finite Rayleigh data for the exported non-diagonal 2x2 Gram fixture.
-/
noncomputable def exportedToyGramTwoByTwoRayleighData
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real) :
    LocalizedWeilFiniteRayleighData (Fin 2) :=
  finiteGramRayleighData coordinate exportedToyGramTwoByTwoFeature

/--
The exported 2x2 Gram fixture has the expected two-square quadratic form.
-/
theorem exportedToyGramTwoByTwoRayleighData_quadraticForm
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (f : SchwartzLineTestFunction) :
    (exportedToyGramTwoByTwoRayleighData coordinate).quadraticForm f =
      (coordinate f 0 + coordinate f 1) ^ 2 + (coordinate f 1) ^ 2 := by
  rw [exportedToyGramTwoByTwoRayleighData,
    finiteGramRayleighData_quadraticForm,
    exportedToyGramTwoByTwoFeature_quadratic]

/--
Build a localized finite-Rayleigh target from the exported 2x2 Gram fixture.

This is still a toy fixture: the residual-identification equation is supplied
as an explicit hypothesis.
-/
noncomputable def exportedToyGramTwoByTwoRayleighTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          ((coordinate f 0 + coordinate f 1) ^ 2 + (coordinate f 1) ^ 2) =
            formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFiniteRayleighTarget formulaData (Fin 2) where
  admissible := admissible
  rayleighData := exportedToyGramTwoByTwoRayleighData coordinate
  rayleighQuadratic_eq_residualSide_on_admissible := by
    intro f hf
    calc
      (exportedToyGramTwoByTwoRayleighData coordinate).quadraticForm f =
          (coordinate f 0 + coordinate f 1) ^ 2 + (coordinate f 1) ^ 2 :=
        exportedToyGramTwoByTwoRayleighData_quadraticForm coordinate f
      _ = formulaData.sideData.residualSide f :=
        rayleigh_eq_residualSide_on_admissible f hf
  restricted_positivity_implies_RHOn_univ :=
    restricted_positivity_implies_RHOn_univ

/--
The exported 2x2 Gram fixture gives support-restricted residual positivity once
the residual-identification equation is supplied.
-/
noncomputable def exportedToyGramTwoByTwoSupportRestrictedFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          ((coordinate f 0 + coordinate f 1) ^ 2 + (coordinate f 1) ^ 2) =
            formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True)) :
    SupportRestrictedFormulaResidualPositivityData formulaData :=
  (exportedToyGramTwoByTwoRayleighTarget
    coordinate
    admissible
    rayleigh_eq_residualSide_on_admissible
    restricted_positivity_implies_RHOn_univ)
    |>.toSupportRestrictedFormulaResidualPositivityData

/--
Build the exported 2x2 Gram/Rayleigh target from a residual identity stated in
source notation.
-/
noncomputable def exportedToyGramTwoByTwoSourceResidualRayleighTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          ((coordinate f 0 + coordinate f 1) ^ 2 + (coordinate f 1) ^ 2) =
            sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFiniteRayleighTarget formulaData (Fin 2) :=
  LocalizedWeilFiniteRayleighTarget.ofSourceResidualSideEq
    sourceResidualSide
    residualSide_eq_source
    admissible
    (exportedToyGramTwoByTwoRayleighData coordinate)
    (by
      intro f hf
      calc
        (exportedToyGramTwoByTwoRayleighData coordinate).quadraticForm f =
            (coordinate f 0 + coordinate f 1) ^ 2 + (coordinate f 1) ^ 2 :=
          exportedToyGramTwoByTwoRayleighData_quadraticForm coordinate f
        _ = sourceResidualSide f :=
          rayleigh_eq_sourceResidualSide_on_admissible f hf)
    restricted_source_positivity_implies_RHOn_univ

/--
The exported 2x2 source-residual fixture gives support-restricted residual
positivity after normalization to formula residual notation.
-/
noncomputable def exportedToyGramTwoByTwoSourceResidualSupportRestrictedFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          ((coordinate f 0 + coordinate f 1) ^ 2 + (coordinate f 1) ^ 2) =
            sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    SupportRestrictedFormulaResidualPositivityData formulaData :=
  (exportedToyGramTwoByTwoSourceResidualRayleighTarget
    sourceResidualSide
    residualSide_eq_source
    coordinate
    admissible
    rayleigh_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ)
    |>.toSupportRestrictedFormulaResidualPositivityData

/--
Pointwise residual nonnegativity from the exported 2x2 source-residual fixture.
-/
theorem exportedToyGramTwoByTwo_sourceResidual_residual_nonneg_on_admissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          ((coordinate f 0 + coordinate f 1) ^ 2 + (coordinate f 1) ^ 2) =
            sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (f : SchwartzLineTestFunction)
    (hf : admissible f) :
    0 <= formulaData.sideData.residualSide f :=
  (exportedToyGramTwoByTwoSourceResidualSupportRestrictedFormulaResidualPositivityData
    sourceResidualSide
    residualSide_eq_source
    coordinate
    admissible
    rayleigh_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ)
    |>.residual_nonneg_on_admissible f hf

/--
Pointwise residual nonnegativity obtained from the exported 2x2 Gram fixture.
-/
theorem exportedToyGramTwoByTwo_residual_nonneg_on_admissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          ((coordinate f 0 + coordinate f 1) ^ 2 + (coordinate f 1) ^ 2) =
            formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True))
    (f : SchwartzLineTestFunction)
    (hf : admissible f) :
    0 <= formulaData.sideData.residualSide f :=
  (exportedToyGramTwoByTwoSupportRestrictedFormulaResidualPositivityData
    coordinate
    admissible
    rayleigh_eq_residualSide_on_admissible
    restricted_positivity_implies_RHOn_univ)
    |>.residual_nonneg_on_admissible f hf

/--
For the exported 2x2 Gram fixture, zero residual on the admissible class is
equivalent to vanishing of both finite coordinates.
-/
theorem exportedToyGramTwoByTwo_residual_eq_zero_iff_coordinate_zero_on_admissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          ((coordinate f 0 + coordinate f 1) ^ 2 + (coordinate f 1) ^ 2) =
            formulaData.sideData.residualSide f)
    (f : SchwartzLineTestFunction)
    (hf : admissible f) :
    formulaData.sideData.residualSide f = 0 <->
      coordinate f 0 = 0 /\ coordinate f 1 = 0 := by
  rw [← rayleigh_eq_residualSide_on_admissible f hf]
  exact exportedToyGramTwoByTwoSquares_eq_zero_iff (coordinate f)

/--
For the exported 2x2 source-residual fixture, zero formula residual on the
admissible class is equivalent to vanishing of both finite coordinates.
-/
theorem exportedToyGramTwoByTwo_sourceResidual_residual_eq_zero_iff_coordinate_zero_on_admissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coordinate : SchwartzLineTestFunction -> Fin 2 -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleigh_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          ((coordinate f 0 + coordinate f 1) ^ 2 + (coordinate f 1) ^ 2) =
            sourceResidualSide f)
    (f : SchwartzLineTestFunction)
    (hf : admissible f) :
    formulaData.sideData.residualSide f = 0 <->
      coordinate f 0 = 0 /\ coordinate f 1 = 0 := by
  rw [residualSide_eq_source f]
  rw [← rayleigh_eq_sourceResidualSide_on_admissible f hf]
  exact exportedToyGramTwoByTwoSquares_eq_zero_iff (coordinate f)

end RiemannHypothesisProject
