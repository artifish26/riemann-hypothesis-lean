# Adversarial Verification

This directory contains an independent red-team review of the release claims.
Its purpose is to test theorem identity, explicit assumptions, multiplicity,
convergence, normalization, dependency direction, and the distinction between
checked equivalences and open conclusions.

The review does not treat a green build, theorem name, module count, or progress
percentage as mathematical validation. Each report traces representative Lean
declarations and records the scope that survives inspection.

## Reports

- `BASELINE_AUDIT_2026-07-15.md` records the initial mechanical and endpoint
  checks.
- `A1_ZERO_COUNTING_AUDIT_2026-07-15.md` audits multiplicity-aware zero
  counting.
- `A2_P_SERIES_AUDIT_2026-07-15.md` audits zero-side summability.
- `A3_FORMULA_IDENTITY_AUDIT_2026-07-15.md` audits the selected Guinand-Weil
  identity.
- `A4_BURNOL_FORMULA_BRIDGE_FINDING_2026-07-15.md` records the fixed-support
  positivity bridge finding and its resolution.
- `A5_CROSS_STREAM_RECONCILIATION_2026-07-16.md` reconciles the four theorem
  streams and leaves global positivity open.
- `FOUR_STREAM_AUDIT_PLAN.md` preserves the audit protocol and final register.

The final scoped verdicts are:

| Track | Verdict |
|---|---|
| Zero-counting / usable growth | `VERIFIED_WITH_SCOPE` |
| P-series / zero-side summability | `VERIFIED` |
| Selected Guinand-Weil formula | `VERIFIED` |
| Fixed-support residual positivity | `VERIFIED_WITH_SCOPE` |
| Global Li/Weil positivity | `OPEN / RH_HARD` |

These verdicts do not constitute a proof of the Riemann Hypothesis.

## Repeatable checks

From the repository root:

```text
lake build
lake env lean ADVERSARIAL/EndpointAudit.lean
lake env lean ADVERSARIAL/A4BurnolFormulaBridgeAudit.lean
rg -n "\b(sorry|axiom|admit)\b" RiemannHypothesisProject --glob "*.lean"
git diff --check
```

The Lean audit consumers are intentionally outside the production import graph.
