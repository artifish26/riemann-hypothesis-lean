# Release verification

`PublicationAxiomAudit.lean` imports representative production endpoints,
including the Hardy endpoint, and prints their axiom dependencies.
`SuzukiS4AxiomAudit.lean` separately checks the experimental S4 publication
wrappers. Run both from the repository root with:

```text
lake env lean RELEASE/PublicationAxiomAudit.lean
lake env lean RELEASE/SuzukiS4AxiomAudit.lean
```

`HARDY.md` records the checked critical-line-zero infinitude endpoint.
`SUZUKI_S4.md` records the exact compact-window S4 surface, its computational
trust boundary, and its global limits. `RIGIDITY_RIG1.md` records the separate
paper-level first-crossing result and explicitly identifies it as non-Lean.

The public release relies on reproducible source and continuous-integration
results rather than machine-specific local build logs. Production,
experimental Lean, and paper-only claims remain separate.
