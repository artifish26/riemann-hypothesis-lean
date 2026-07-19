import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Order.Filter.AtTopBot.Basic
import RiemannHypothesisProject.RiemannVonMangoldtHeightTarget
import RiemannHypothesisProject.RiemannVonMangoldt.AxisWindows
import RiemannHypothesisProject.RiemannVonMangoldt.RealAxisCleanup
import RiemannHypothesisProject.RiemannVonMangoldt.EtaAlternating
import RiemannHypothesisProject.RiemannVonMangoldt.ZModTwoHalfTail
import RiemannHypothesisProject.RiemannVonMangoldt.OpenUnitIntervalZetaEndpoints
import RiemannHypothesisProject.RiemannVonMangoldt.RealAxisEndpoints
import RiemannHypothesisProject.ZetaConjugation
import RiemannHypothesisProject.ZetaSetup

/-!
# Axis/trivial-zero decomposition facade

This compatibility facade re-exports the focused Riemann-von-Mangoldt axis
window, eta/ZMod bridge, open-unit-interval zeta, and real-axis endpoint modules
split out of the original discovery file.
-/
