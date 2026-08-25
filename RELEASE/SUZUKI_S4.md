# Suzuki S4 Compact-Window Release

Status: `EXPERIMENTAL / CHECKED / S4 REACHED`

Decision: `PUBLISH AND FREEZE`

Release: `v0.3.0`

## Result

The source-package-free publication surface is
`RiemannHypothesisProject/Experiments/M100/SuzukiYoshidaS4Publication.lean`.
It instantiates X19B's two explicit DF6F source packages with their checked
inhabitants and exposes a canonical solution family on

```text
SuzukiDF6EInterval = [log(2)/2, suzukiProjectAStar]
```

and the closed complex spectral unit disk `||w|| <= 1`.

The principal released declarations are:

- `suzukiS4CompactWindowSolution`;
- `suzukiS4CompactWindowSolution_norm_le_fourThousand`, proving the uniform
  source-energy bound `||u_w(a)|| <= 4000`;
- `suzukiS4CompactWindowSolutionMap_lipschitz`, proving fixed-radius
  Lipschitz dependence on the spectral parameter;
- `suzukiS4CompactWindowSolutionMap_isCompact_range`, proving compact image
  of the closed unit disk at each released radius; and
- `eventually_suzukiS4CompactWindowSolution_close_from_below`, proving
  directed strong radius continuity from below at interior released radii
  after canonical completion transport.

The checked dependency chain is:

```text
B3Q-G + B3F-E + B3F-F -> S1
       B3R-E + B3R + B4 -> S2
                    DF6E + DF6F -> S3
                              X19B -> S4
```

The S3 coercivity and genuine-source identification remain part of this
cumulative release. X19B adds the normalized bounded-window Fredholm family,
parameter control, compact image, and radius continuity needed for S4.

## Trust boundary

The upstream finite residual inputs are exact rational data checked in Lean.
Their independent regeneration produced the same source byte-for-byte with
SHA-256
`C0C68CC2857E29064AD518EE36C825CDD0E423F92D4989C8A805D16741BD4CDA`.
The certificate chain retains its declared compiler-backed `native_decide`
boundary. The S4 wrappers add no new project axiom or source premise.

Run `RELEASE/SuzukiS4AxiomAudit.lean` to inspect the four principal endpoint
dependencies. The independent scope report is
`ADVERSARIAL/S4_SUZUKI_PUBLICATION_AUDIT_2026-08-21.md`.

## Claim boundary

S4 is a compact-window experimental milestone. It does not prove:

- interval-`L2` realization of every source-energy completion vector;
- nondegeneracy for every radius `a > 0`;
- a completed-zeta or `z^2 xi/xi'` limit theorem;
- global Weil positivity; or
- the Riemann Hypothesis.

The separate all-radius review found no named propagation, first-crossing
contradiction, determinant, or eventual-positivity mechanism. The Suzuki
programme is therefore frozen at S4 unless a later independent theorem
supplies such a mechanism.
