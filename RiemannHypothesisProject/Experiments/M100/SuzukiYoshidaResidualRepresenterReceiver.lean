import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaComparisonEnergyCompletionSquare
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaParityFarTargets
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# B3R-E ambient residual-representer receiver

This module joins the two frozen DF6D4 residual blocks into one physical tail
sequence and specializes Fréchet--Riesz representation to the exact closed
even and odd ambient tail spaces from B3T.  Existence of the required bounded
functional remains an explicit premise.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set
open scoped ComplexConjugate

/-- Physical Yoshida modes in the B3R residual tail. -/
abbrev SuzukiDF6D5B3RTailMode := {n : Nat // 45 ≤ n}

/-- The complete even residual coefficient sequence.  It retains the frozen
Galerkin solve residual on modes `45,...,300` and uses the analytic residual
column from mode `301` onward. -/
def suzukiDF6D5B3REvenFullResidualCoefficient
    (i : Fin 45) (n : SuzukiDF6D5B3RTailMode) : Real :=
  if h : n.1 < 301 then
    suzukiDF6D4EvenGalerkinSolveResidual
      ⟨n.1 - 45, by omega⟩ i
  else
    suzukiDF6D4EvenResidualColumn n.1 i

/-- The complete odd residual coefficient sequence. -/
def suzukiDF6D5B3ROddFullResidualCoefficient
    (i : Fin 44) (n : SuzukiDF6D5B3RTailMode) : Real :=
  if h : n.1 < 301 then
    suzukiDF6D4OddGalerkinSolveResidual
      ⟨n.1 - 45, by omega⟩ i
  else
    suzukiDF6D4OddResidualColumn n.1 i

/-- On the frozen Galerkin window, the full even sequence is exactly the
solve residual. -/
@[simp]
theorem suzukiDF6D5B3REvenFullResidualCoefficient_galerkin
    (i : Fin 45) (j : Fin 256) :
    suzukiDF6D5B3REvenFullResidualCoefficient i
        ⟨suzukiDF6D4GalerkinMode j, by
          simp [suzukiDF6D4GalerkinMode]⟩ =
      suzukiDF6D4EvenGalerkinSolveResidual j i := by
  unfold suzukiDF6D5B3REvenFullResidualCoefficient
  rw [dif_pos (by
    have := j.isLt
    simp [suzukiDF6D4GalerkinMode]
    omega)]
  congr 1
  apply Fin.ext
  simp [suzukiDF6D4GalerkinMode]

/-- On the frozen Galerkin window, the full odd sequence is exactly the solve
residual. -/
@[simp]
theorem suzukiDF6D5B3ROddFullResidualCoefficient_galerkin
    (i : Fin 44) (j : Fin 256) :
    suzukiDF6D5B3ROddFullResidualCoefficient i
        ⟨suzukiDF6D4GalerkinMode j, by
          simp [suzukiDF6D4GalerkinMode]⟩ =
      suzukiDF6D4OddGalerkinSolveResidual j i := by
  unfold suzukiDF6D5B3ROddFullResidualCoefficient
  rw [dif_pos (by
    have := j.isLt
    simp [suzukiDF6D4GalerkinMode]
    omega)]
  congr 1
  apply Fin.ext
  simp [suzukiDF6D4GalerkinMode]

/-- From physical mode `301` onward, the full even sequence is exactly the
frozen residual column. -/
@[simp]
theorem suzukiDF6D5B3REvenFullResidualCoefficient_of_ge
    (i : Fin 45) (mode : Nat) (hmode : 301 ≤ mode) :
    suzukiDF6D5B3REvenFullResidualCoefficient i
        ⟨mode, by omega⟩ =
      suzukiDF6D4EvenResidualColumn mode i := by
  simp [suzukiDF6D5B3REvenFullResidualCoefficient,
    not_lt.mpr hmode]

/-- From physical mode `301` onward, the full odd sequence is exactly the
frozen residual column. -/
@[simp]
theorem suzukiDF6D5B3ROddFullResidualCoefficient_of_ge
    (i : Fin 44) (mode : Nat) (hmode : 301 ≤ mode) :
    suzukiDF6D5B3ROddFullResidualCoefficient i
        ⟨mode, by omega⟩ =
      suzukiDF6D4OddResidualColumn mode i := by
  simp [suzukiDF6D5B3ROddFullResidualCoefficient,
    not_lt.mpr hmode]

/-- The exact Hilbert subtype of the ambient even Yoshida tail. -/
abbrev SuzukiDF6D5B3REvenAmbientFarL2 :=
  suzukiDF6D5B3TEvenAmbientFarSubspace

/-- The exact Hilbert subtype of the ambient odd Yoshida tail. -/
abbrev SuzukiDF6D5B3ROddAmbientFarL2 :=
  suzukiDF6D5B3TOddAmbientFarSubspace

/-- A physical even tail mode bundled in the exact ambient even far space. -/
def suzukiDF6D5B3REvenAmbientMode
    (n : SuzukiDF6D5B3RTailMode) : SuzukiDF6D5B3REvenAmbientFarL2 :=
  ⟨suzukiYoshidaEvenL2 suzukiProjectAStar
      suzukiProjectAStar_pos n.1, by
    change
      suzukiYoshidaEvenL2 suzukiProjectAStar
          suzukiProjectAStar_pos n.1 ∈
        (Submodule.span Complex
          (Set.range fun m : SuzukiDF6D5B3RTailMode =>
            suzukiYoshidaEvenL2 suzukiProjectAStar
              suzukiProjectAStar_pos m.1)).topologicalClosure
    exact
      (Submodule.span Complex
        (Set.range fun m : SuzukiDF6D5B3RTailMode =>
          suzukiYoshidaEvenL2 suzukiProjectAStar
            suzukiProjectAStar_pos m.1)).le_topologicalClosure
        (Submodule.subset_span (Set.mem_range_self n))⟩

/-- A physical odd tail mode bundled in the exact ambient odd far space. -/
def suzukiDF6D5B3ROddAmbientMode
    (n : SuzukiDF6D5B3RTailMode) : SuzukiDF6D5B3ROddAmbientFarL2 :=
  ⟨suzukiYoshidaOddL2 suzukiProjectAStar
      suzukiProjectAStar_pos n.1, by
    change
      suzukiYoshidaOddL2 suzukiProjectAStar
          suzukiProjectAStar_pos n.1 ∈
        (Submodule.span Complex
          (Set.range fun m : SuzukiDF6D5B3RTailMode =>
            suzukiYoshidaOddL2 suzukiProjectAStar
              suzukiProjectAStar_pos m.1)).topologicalClosure
    exact
      (Submodule.span Complex
        (Set.range fun m : SuzukiDF6D5B3RTailMode =>
          suzukiYoshidaOddL2 suzukiProjectAStar
            suzukiProjectAStar_pos m.1)).le_topologicalClosure
        (Submodule.subset_span (Set.mem_range_self n))⟩

/-- The canonical Fréchet--Riesz representer of a bounded functional on the
ambient even tail. -/
def suzukiDF6D5B3REvenAmbientRepresenter
    (functional : SuzukiDF6D5B3REvenAmbientFarL2 →L[Complex] Complex) :
    SuzukiDF6D5B3REvenAmbientFarL2 := by
  letI : CompleteSpace SuzukiDF6D5B3REvenAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TEvenAmbientFarSubspace.completeSpace_coe
  exact
    (InnerProductSpace.toDual Complex
      SuzukiDF6D5B3REvenAmbientFarL2).symm functional

/-- The canonical Fréchet--Riesz representer of a bounded functional on the
ambient odd tail. -/
def suzukiDF6D5B3ROddAmbientRepresenter
    (functional : SuzukiDF6D5B3ROddAmbientFarL2 →L[Complex] Complex) :
    SuzukiDF6D5B3ROddAmbientFarL2 := by
  letI : CompleteSpace SuzukiDF6D5B3ROddAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TOddAmbientFarSubspace.completeSpace_coe
  exact
    (InnerProductSpace.toDual Complex
      SuzukiDF6D5B3ROddAmbientFarL2).symm functional

/-- The even representer realizes its functional by the ambient inner
product. -/
theorem suzukiDF6D5B3REvenAmbientRepresenter_pairing
    (functional : SuzukiDF6D5B3REvenAmbientFarL2 →L[Complex] Complex)
    (v : SuzukiDF6D5B3REvenAmbientFarL2) :
    inner Complex (suzukiDF6D5B3REvenAmbientRepresenter functional) v =
      functional v := by
  letI : CompleteSpace SuzukiDF6D5B3REvenAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TEvenAmbientFarSubspace.completeSpace_coe
  unfold suzukiDF6D5B3REvenAmbientRepresenter
  exact InnerProductSpace.toDual_symm_apply

/-- The odd representer realizes its functional by the ambient inner
product. -/
theorem suzukiDF6D5B3ROddAmbientRepresenter_pairing
    (functional : SuzukiDF6D5B3ROddAmbientFarL2 →L[Complex] Complex)
    (v : SuzukiDF6D5B3ROddAmbientFarL2) :
    inner Complex (suzukiDF6D5B3ROddAmbientRepresenter functional) v =
      functional v := by
  letI : CompleteSpace SuzukiDF6D5B3ROddAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TOddAmbientFarSubspace.completeSpace_coe
  unfold suzukiDF6D5B3ROddAmbientRepresenter
  exact InnerProductSpace.toDual_symm_apply

/-- Fréchet--Riesz preserves the norm of the even ambient functional. -/
theorem norm_suzukiDF6D5B3REvenAmbientRepresenter
    (functional : SuzukiDF6D5B3REvenAmbientFarL2 →L[Complex] Complex) :
    ‖suzukiDF6D5B3REvenAmbientRepresenter functional‖ = ‖functional‖ := by
  letI : CompleteSpace SuzukiDF6D5B3REvenAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TEvenAmbientFarSubspace.completeSpace_coe
  unfold suzukiDF6D5B3REvenAmbientRepresenter
  exact
    (InnerProductSpace.toDual Complex
      SuzukiDF6D5B3REvenAmbientFarL2).symm.norm_map functional

/-- Fréchet--Riesz preserves the norm of the odd ambient functional. -/
theorem norm_suzukiDF6D5B3ROddAmbientRepresenter
    (functional : SuzukiDF6D5B3ROddAmbientFarL2 →L[Complex] Complex) :
    ‖suzukiDF6D5B3ROddAmbientRepresenter functional‖ = ‖functional‖ := by
  letI : CompleteSpace SuzukiDF6D5B3ROddAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TOddAmbientFarSubspace.completeSpace_coe
  unfold suzukiDF6D5B3ROddAmbientRepresenter
  exact
    (InnerProductSpace.toDual Complex
      SuzukiDF6D5B3ROddAmbientFarL2).symm.norm_map functional

/-- A bounded even-tail functional with the declared frozen modal values has
a representer with exactly the full residual coefficients. -/
theorem suzukiDF6D5B3REvenAmbientRepresenter_coefficient
    (i : Fin 45)
    (functional : SuzukiDF6D5B3REvenAmbientFarL2 →L[Complex] Complex)
    (hcoeff : ∀ n : SuzukiDF6D5B3RTailMode,
      functional (suzukiDF6D5B3REvenAmbientMode n) =
        (suzukiDF6D5B3REvenFullResidualCoefficient i n : Complex))
    (n : SuzukiDF6D5B3RTailMode) :
    inner Complex (suzukiDF6D5B3REvenAmbientMode n)
        (suzukiDF6D5B3REvenAmbientRepresenter functional) =
      (suzukiDF6D5B3REvenFullResidualCoefficient i n : Complex) := by
  rw [← inner_conj_symm,
    suzukiDF6D5B3REvenAmbientRepresenter_pairing, hcoeff]
  simp

/-- A bounded odd-tail functional with the declared frozen modal values has
a representer with exactly the full residual coefficients. -/
theorem suzukiDF6D5B3ROddAmbientRepresenter_coefficient
    (i : Fin 44)
    (functional : SuzukiDF6D5B3ROddAmbientFarL2 →L[Complex] Complex)
    (hcoeff : ∀ n : SuzukiDF6D5B3RTailMode,
      functional (suzukiDF6D5B3ROddAmbientMode n) =
        (suzukiDF6D5B3ROddFullResidualCoefficient i n : Complex))
    (n : SuzukiDF6D5B3RTailMode) :
    inner Complex (suzukiDF6D5B3ROddAmbientMode n)
        (suzukiDF6D5B3ROddAmbientRepresenter functional) =
      (suzukiDF6D5B3ROddFullResidualCoefficient i n : Complex) := by
  rw [← inner_conj_symm,
    suzukiDF6D5B3ROddAmbientRepresenter_pairing, hcoeff]
  simp

end

end RiemannHypothesisProject.Experiments.M100
