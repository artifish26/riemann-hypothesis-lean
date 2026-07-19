# Release verification

`PublicationAxiomAudit.lean` imports representative public endpoints and prints
their axiom dependencies. Run it from the repository root with:

```text
lake env lean RELEASE/PublicationAxiomAudit.lean
```

The public release relies on reproducible source and continuous-integration
results rather than machine-specific local build logs.
