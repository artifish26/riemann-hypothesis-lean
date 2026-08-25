# S4 Suzuki Publication Audit — 2026-08-21

Verdict: `VERIFIED_WITH_SCOPE`

Milestone decision: `S4 REACHED`

Programme decision: `PUBLISH AND FREEZE`; global extension `NO-GO`.

## Claim Audited

The audit tested whether the closed X19B bounded-window construction can be
released on the genuine DF6F source surface without a hidden source premise,
whether experimental and production imports remain separated, and whether
the release package states its certificate trust boundary and global
limitations accurately.

## Finding Record

ID: `ADV-SUZ-S4-001`

Track: experimental Suzuki S4 publication boundary.

Severity: `P2`.

Status: `ACCEPTED_SCOPE`.

Claim: “S4 is reached: X19B is proved on the genuine source surface and the
released theorem is a compact-window result, not global positivity or RH.”

Lean declarations:
`suzukiS4CompactWindowSolution_norm_le_fourThousand`,
`suzukiS4CompactWindowSolutionMap_lipschitz`,
`suzukiS4CompactWindowSolutionMap_isCompact_range`, and
`eventually_suzukiS4CompactWindowSolution_close_from_below`.

Explicit premises: radius membership in `SuzukiDF6EInterval`, spectral
membership `||w|| <= 1`, and the local hypotheses needed for directed
continuity. There is no source-package theorem argument on the S4 surface.

Transitive source inputs: the DF6F inhabitants
`suzukiYoshidaExponentialFormCoreSourceAt_boundaryCutoff` and
`suzukiEquation25SourceIdentityAt_proved`, the S1--S3 coercivity and source
identification chain, and the upstream exact rational certificate boundary.

Consumer: `RELEASE/SUZUKI_S4.md`, which is the curated publication ledger;
there is deliberately no production Lean consumer or import.

Attack: expand the wrapper, search for uninstantiated proposition arguments,
print endpoint axioms, challenge the carrier and parameter quantifiers, scan
for experiment-to-production imports, and test whether the prose infers an
all-radius or RH conclusion.

Evidence: the signatures consume the checked DF6F inhabitants internally;
focused and full builds pass; the axiom report adds no project axiom; the
production import scan is empty; and the release limits radius, spectral
parameter, carrier, and global inference explicitly.

Verdict: `VERIFIED_WITH_SCOPE`. S4 is justified as an experimental
compact-window publication milestone. It is not production promotion and does
not close M100.

Corrective action: add the source-package-free publication wrapper, stable S4 ledger,
and explicit post-S4 `NO-GO`/freeze decision; reconcile current-status docs.

Score consequence: `retain`; formula-side residual positivity remains `90%`.

## Theorem-Surface Findings

X19B itself deliberately retains two explicit packages:

```text
SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar
SuzukiEquation25SourceIdentityAt suzukiProjectAStar
```

Both have checked DF6F inhabitants. The audited publication module instantiates
them through
`suzukiYoshidaExponentialFormCoreSourceAt_boundaryCutoff` and
`suzukiEquation25SourceIdentityAt_proved`. Its public theorem endpoints have
no corresponding theorem arguments. The released conclusions are exactly:

- existence of the canonical solution on the named compact radius window and
  closed complex unit disk;
- the uniform source-energy norm bound `4000`;
- fixed-radius Lipschitz dependence and compact image in the source-energy
  completion; and
- directed strong radius continuity from below at interior radii after the
  checked completion transport.

No theorem asserts all-radius nondegeneracy, global positivity, a completed-
zeta limit, or RH.

## Mechanical Checks

Audit baseline: `fac316998b5b3c069ed6c74030e60d747b19a572` on
`codex/x19b-bounded-window-solutions`, plus the S4 release paths audited here.

The following checks passed:

1. Focused build of
   `RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaS4Publication`:
   success, `5284` jobs.
2. Temporary theorem-signature and `#print axioms` audit of the norm,
   Lipschitz, compact-image, and directed-radius-continuity endpoints:
   success, `5285` jobs; the temporary module was removed.
3. Full default `lake build`: success, `3945` jobs.
4. Placeholder scan of the X19B and S4 publication modules: no `sorry`,
   `admit`, new `axiom`, `TODO`, or `FIXME` marker.
5. Production-boundary scan: no production Lean file imports an experiment or
   adversarial module.
6. `git diff --check`: passed.

The default project aggregate intentionally excludes experiment modules, so
the focused S4 build is the relevant check of the release theorem surface;
the full build separately verifies that the production tree remains intact.

## Axiom And Computational Boundary

The S4 endpoint audit exposed Lean's standard `propext`, `Classical.choice`,
and `Quot.sound`, plus the already-declared `native_decide` boundary used by
the upstream exact certificate chain. It exposed no new S4 or X19B axiom and
no uninstantiated source package.

The DF6D4 exact rational data had already passed independent numerical
closeout with byte-identical Arb regeneration and SHA-256
`C0C68CC2857E29064AD518EE36C825CDD0E423F92D4989C8A805D16741BD4CDA`.
During this audit the documented Arb command was tried again. The installed
Python 3.12 runtime cannot load the generator's pinned Python 3.11
`python-flint==0.8.0` extension, and the attempt stopped immediately before
certificate generation. The release records that compatibility prerequisite
and the successful prior independent reproduction rather than misreporting a
new numerical run.

## Scope Challenges

- **Genuine source surface:** passed. The publication wrapper consumes the
  checked DF6F source inhabitants.
- **Domain and norm:** passed with scope. Results live in Suzuki's shifted
  source-energy completion, not an asserted interval-`L2` realization.
- **Parameter scope:** passed with scope. Radius is restricted to
  `SuzukiDF6EInterval`; spectral parameter is restricted to the closed unit
  disk.
- **Production boundary:** passed. The release remains experimental and no
  production module imports it.
- **Global inference:** rejected. Compact-window coercivity and bounded
  Fredholm control do not yield all-radius no-crossing or RH.

## Global Go/No-Go

The audit found no checked or precisely sourced mechanism that propagates the
compact-window result to every radius. In particular, S1--S4 do not supply a
first-crossing contradiction, a controlled dangerous-subspace reduction, a
determinant/Weyl criterion equivalent to source degeneracy, or eventual
positivity with a finite certified bridge.

The charter's stop condition therefore applies: publish the compact-window
result, freeze the Suzuki programme, retain the verified evidence, and do not
open the all-radius prospect without a later, independently justified named
mechanism.
