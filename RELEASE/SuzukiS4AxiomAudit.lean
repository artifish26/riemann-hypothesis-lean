import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaS4Publication

/-!
# Suzuki S4 release axiom audit

Run with:

`lake env lean RELEASE/SuzukiS4AxiomAudit.lean`

This audit checks the source-package-free S4 publication wrappers and prints
the logical and computational dependency boundary of their principal
endpoints.  The module is audit-only and is not imported by production code.
-/

open RiemannHypothesisProject.Experiments.M100

#check suzukiS4CompactWindowSolution_norm_le_fourThousand
#check suzukiS4CompactWindowSolutionMap_lipschitz
#check suzukiS4CompactWindowSolutionMap_isCompact_range
#check eventually_suzukiS4CompactWindowSolution_close_from_below

#print axioms suzukiS4CompactWindowSolution_norm_le_fourThousand
#print axioms suzukiS4CompactWindowSolutionMap_lipschitz
#print axioms suzukiS4CompactWindowSolutionMap_isCompact_range
#print axioms eventually_suzukiS4CompactWindowSolution_close_from_below
