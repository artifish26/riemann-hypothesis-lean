import RiemannHypothesisProject.LiCriterion.ZetaLiCoefficient

/-!
# M100-X00 exact synthetic-zero no-go witness

This experimental module evaluates the project Li summand on the rational
off-line quartet `0.9 ± 0.001i`, `0.1 ± 0.001i`. The exact negative coefficient is
a route filter for symmetry-only positivity arguments. These points are not
claimed to be zeta zeroes, and this module has no production imports.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open ComplexCompactExhaustion

/-- The finite Li coefficient of the conjugation- and reflection-closed
synthetic quartet `0.9 ± 0.001i`, `0.1 ± 0.001i`. -/
noncomputable def syntheticOffLineQuartetLiCoefficient (n : Nat) : Real :=
  (zetaLiComplexSummand ((9 : Complex) / 10 + Complex.I / 1000) n +
    zetaLiComplexSummand ((9 : Complex) / 10 - Complex.I / 1000) n +
    zetaLiComplexSummand ((1 : Complex) / 10 + Complex.I / 1000) n +
    zetaLiComplexSummand ((1 : Complex) / 10 - Complex.I / 1000) n).re

private theorem zetaLiComplexSummand_two_re (rho : Complex) :
    (zetaLiComplexSummand rho 2).re =
      2 * rho.re / Complex.normSq rho -
        (rho.re ^ 2 - rho.im ^ 2) / Complex.normSq rho ^ 2 := by
  simp only [zetaLiComplexSummand, pow_two, Complex.sub_re, Complex.one_re,
    Complex.mul_re, Complex.inv_re, Complex.sub_im, Complex.one_im,
    Complex.inv_im, zero_sub]
  ring

/-- Exact finite counterexample: functional and conjugation symmetry alone do
not force Li nonnegativity. -/
theorem syntheticOffLineQuartetLiCoefficient_two_neg :
    syntheticOffLineQuartetLiCoefficient 2 < 0 := by
  simp only [syntheticOffLineQuartetLiCoefficient, Complex.add_re,
    zetaLiComplexSummand_two_re]
  norm_num [Complex.normSq_apply]

/-- The corresponding diagonal of the finite Lagarias Li-basis Gram matrix. -/
noncomputable def syntheticOffLineQuartetLiGramDiagonal (n : Nat) : Real :=
  2 * syntheticOffLineQuartetLiCoefficient n

/-- The same exact counterexample as a negative Li-basis Gram coordinate
direction. -/
theorem syntheticOffLineQuartetLiGramDiagonal_two_neg :
    syntheticOffLineQuartetLiGramDiagonal 2 < 0 := by
  unfold syntheticOffLineQuartetLiGramDiagonal
  nlinarith [syntheticOffLineQuartetLiCoefficient_two_neg]

end M100
end Experiments
end RiemannHypothesisProject
