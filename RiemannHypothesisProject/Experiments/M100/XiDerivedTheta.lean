import RiemannHypothesisProject.RiemannVonMangoldt.RiemannXi

/-!
# M100-X12: an explicit xi-derived meromorphic source

Suzuki's canonical-system paper starts from

`E_omega(z) = xi(1/2 + omega - i z)`

and the quotient

`Theta_omega(z) = xi(1/2 - omega - i z) / xi(1/2 + omega - i z)`.

This experimental module records only definition-level consequences of the
functional equation.  It does not assert that `Theta_omega` is inner, construct
a de Branges space or canonical system, prove Hermite--Biehler positivity, or
identify zeta zeros with a real spectrum.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

namespace M100X12

noncomputable section

open Complex

/-- Suzuki's shifted xi entire function `E_omega`. -/
def suzukiXiPlus (omega : Real) (z : Complex) : Complex :=
  riemannXi ((1 / 2 : Complex) + (omega : Complex) - I * z)

/-- The reflected xi shift used in the numerator of `Theta_omega`. -/
def suzukiXiMinus (omega : Real) (z : Complex) : Complex :=
  riemannXi ((1 / 2 : Complex) - (omega : Complex) - I * z)

/-- Suzuki's xi quotient, represented as a total Lean function.

The source treats this quotient meromorphically.  Pointwise identities below
therefore name the required nonvanishing domain explicitly.
-/
def suzukiTheta (omega : Real) (z : Complex) : Complex :=
  suzukiXiMinus omega z / suzukiXiPlus omega z

/-- The even xi combination `A_omega` from Suzuki's normalization. -/
def suzukiA (omega : Real) (z : Complex) : Complex :=
  (suzukiXiPlus omega z + suzukiXiMinus omega z) / 2

/-- The odd xi combination `B_omega` from Suzuki's normalization. -/
def suzukiB (omega : Real) (z : Complex) : Complex :=
  I / 2 * (suzukiXiPlus omega z - suzukiXiMinus omega z)

/-- Suzuki's positive xi shift is entire on the complex plane. -/
theorem differentiable_suzukiXiPlus (omega : Real) :
    Differentiable Complex (suzukiXiPlus omega) := by
  unfold suzukiXiPlus
  exact differentiable_riemannXi.comp (by fun_prop)

/-- Suzuki's reflected xi shift is entire on the complex plane. -/
theorem differentiable_suzukiXiMinus (omega : Real) :
    Differentiable Complex (suzukiXiMinus omega) := by
  unfold suzukiXiMinus
  exact differentiable_riemannXi.comp (by fun_prop)

/-- The functional equation exchanges the two xi shifts under `z |-> -z`. -/
theorem suzukiXiPlus_neg (omega : Real) (z : Complex) :
    suzukiXiPlus omega (-z) = suzukiXiMinus omega z := by
  rw [suzukiXiPlus, suzukiXiMinus]
  rw [show (1 / 2 : Complex) + (omega : Complex) - I * (-z) =
      1 - ((1 / 2 : Complex) - (omega : Complex) - I * z) by ring]
  exact riemannXi_one_sub _

/-- The reverse exchange of the two xi shifts under `z |-> -z`. -/
theorem suzukiXiMinus_neg (omega : Real) (z : Complex) :
    suzukiXiMinus omega (-z) = suzukiXiPlus omega z := by
  rw [suzukiXiMinus, suzukiXiPlus]
  rw [show (1 / 2 : Complex) - (omega : Complex) - I * (-z) =
      1 - ((1 / 2 : Complex) + (omega : Complex) - I * z) by ring]
  exact riemannXi_one_sub _

/-- Suzuki's `A_omega` is even, unconditionally. -/
theorem suzukiA_neg (omega : Real) (z : Complex) :
    suzukiA omega (-z) = suzukiA omega z := by
  simp only [suzukiA, suzukiXiPlus_neg, suzukiXiMinus_neg]
  ring

/-- Suzuki's `B_omega` is odd, unconditionally. -/
theorem suzukiB_neg (omega : Real) (z : Complex) :
    suzukiB omega (-z) = -suzukiB omega z := by
  simp only [suzukiB, suzukiXiPlus_neg, suzukiXiMinus_neg]
  ring

/-- Pointwise form of Suzuki's meromorphic inversion identity (1.8).

Both shifted xi values are required to be nonzero because division in Lean is
total, whereas the source equality is an equality of meromorphic functions.
-/
theorem suzukiTheta_mul_neg
    (omega : Real) (z : Complex)
    (hplus : suzukiXiPlus omega z ≠ 0)
    (hminus : suzukiXiMinus omega z ≠ 0) :
    suzukiTheta omega z * suzukiTheta omega (-z) = 1 := by
  simp only [suzukiTheta, suzukiXiMinus_neg, suzukiXiPlus_neg]
  field_simp [hplus, hminus]

end

end M100X12

end ComplexCompactExhaustion

end RiemannHypothesisProject
