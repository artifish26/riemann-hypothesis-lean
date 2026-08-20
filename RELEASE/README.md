# Release verification

`PublicationAxiomAudit.lean` imports representative production endpoints and
prints their axiom dependencies. `SuzukiS3AxiomAudit.lean` separately checks
the experimental S3 compositions and prints their axiom dependencies. Run
both from the repository root with:

```text
lake env lean RELEASE/PublicationAxiomAudit.lean
lake env lean RELEASE/SuzukiS3AxiomAudit.lean
```

`SUZUKI_S3.md` records the exact compact-window claim, formerly visible source
premises and their checked inhabitants, computational trust boundary, and
open X19B/S4/global work.

The public release relies on reproducible source and continuous-integration
results rather than machine-specific local build logs. Production and
experimental claims remain separate.
