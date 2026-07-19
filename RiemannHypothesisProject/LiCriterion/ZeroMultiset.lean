import RiemannHypothesisProject.LiCriterion.ZetaZeroMultiplicityConjugation

/-!
# Multiplicity-aware zeta-zero indices

This module records analytic multiplicity in the index type itself.  The full
non-real zeta-zero family is represented by a positive-ordinate copy and its
complex-conjugate copy.  Convergence and cutoff choices are deliberately left
to the later star-convergence module.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open ComplexConjugate

noncomputable section

/-- Expand a family indexed by `alpha` into one index for each unit of its
multiplicity. -/
abbrev MultiplicityIndex (alpha : Type*) (multiplicity : alpha -> Nat) :=
  Sigma fun a : alpha => Fin (multiplicity a)

/-- The underlying distinct index of a multiplicity-expanded index. -/
def MultiplicityIndex.base
    {alpha : Type*} {multiplicity : alpha -> Nat}
    (i : MultiplicityIndex alpha multiplicity) : alpha :=
  i.1

/-- Summing a constant over the expanded fibre is the corresponding natural
multiple. -/
theorem sum_multiplicityIndex_fiber
    {alpha M : Type*} [AddCommMonoid M]
    (multiplicity : alpha -> Nat) (f : alpha -> M) (a : alpha) :
    Finset.univ.sum (fun _ : Fin (multiplicity a) => f a) =
      multiplicity a • f a := by
  simp

/-- Finite sums over multiplicity-expanded fibres agree with the usual
multiplicity-weighted finite sum. -/
theorem sum_multiplicityIndex_fibers
    {alpha M : Type*} [AddCommMonoid M]
    (multiplicity : alpha -> Nat) (f : alpha -> M) (s : Finset alpha) :
    s.sum (fun a => Finset.univ.sum (fun _ : Fin (multiplicity a) => f a)) =
      s.sum (fun a => multiplicity a • f a) := by
  simp

/-- Positive-ordinate zeta zeroes with analytic multiplicity expanded into
the index. -/
abbrev PositiveOrdinateZetaZeroMultiplicityIndex :=
  MultiplicityIndex PositiveOrdinateZetaZeroSubtype
    (fun rho => zetaZeroMultiplicity rho.1)

/-- The signed non-real zeta-zero index: positive zeroes on the left and their
conjugates on the right, with analytic multiplicity already expanded. -/
abbrev SignedZetaZeroMultiplicityIndex :=
  PositiveOrdinateZetaZeroMultiplicityIndex ⊕
    PositiveOrdinateZetaZeroMultiplicityIndex

/-- The actual zeta zero represented by a signed multiplicity index. -/
def signedZetaZeroValue : SignedZetaZeroMultiplicityIndex -> Complex
  | Sum.inl i => (i.1.1 : Complex)
  | Sum.inr i => conj (i.1.1 : Complex)

/-- Every expanded positive index represents a positive-ordinate zeta zero. -/
theorem signedZetaZeroValue_im_pos
    (i : PositiveOrdinateZetaZeroMultiplicityIndex) :
    0 < (signedZetaZeroValue (Sum.inl i)).im :=
  i.1.2

/-- Every expanded conjugate index represents a negative-ordinate zeta zero. -/
theorem signedZetaZeroValue_im_neg
    (i : PositiveOrdinateZetaZeroMultiplicityIndex) :
    (signedZetaZeroValue (Sum.inr i)).im < 0 := by
  simpa [signedZetaZeroValue] using neg_lt_zero.mpr i.1.2

/-- The signed expanded family consists of actual zeta zeroes. -/
theorem signedZetaZeroValue_isZetaZero
    (i : SignedZetaZeroMultiplicityIndex) :
    IsZetaZero (signedZetaZeroValue i) := by
  cases i with
  | inl i => exact i.1.1.property
  | inr i =>
      exact zetaZeroConjugationSymmetry (i.1.1 : Complex) i.1.1.property

/-- A zeta zero with nonzero ordinate is not a project trivial zero. -/
theorem not_isTrivialZetaZero_of_im_ne_zero
    {rho : Complex} (him : Not (rho.im = 0)) :
    Not (IsTrivialZetaZero rho) := by
  rintro ⟨n, rfl⟩
  exact him (by simp)

/-- Every member of the signed expanded family is nontrivial. -/
theorem signedZetaZeroValue_isNontrivialZetaZero
    (i : SignedZetaZeroMultiplicityIndex) :
    IsNontrivialZetaZero (signedZetaZeroValue i) := by
  refine ⟨signedZetaZeroValue_isZetaZero i, ?_, ?_⟩
  · apply not_isTrivialZetaZero_of_im_ne_zero
    cases i with
    | inl i => exact ne_of_gt (signedZetaZeroValue_im_pos i)
    | inr i => exact ne_of_lt (signedZetaZeroValue_im_neg i)
  · intro h
    have him : (signedZetaZeroValue i).im = 0 := by rw [h]; simp
    cases i with
    | inl i => exact (ne_of_gt (signedZetaZeroValue_im_pos i)) him
    | inr i => exact (ne_of_lt (signedZetaZeroValue_im_neg i)) him

/-- Conjugation preserves the analytic multiplicity used by the two signed
copies. -/
theorem signedZetaZeroMultiplicity_conj
    (rho : PositiveOrdinateZetaZeroSubtype) :
    zetaZeroMultiplicity
        ⟨conj (rho : Complex),
          zetaZeroConjugationSymmetry (rho : Complex) rho.1.property⟩ =
      zetaZeroMultiplicity rho.1 :=
  zetaZeroMultiplicity_conj rho.1

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
