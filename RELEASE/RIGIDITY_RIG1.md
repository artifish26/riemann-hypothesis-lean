# RIG0--RIG1 First-Crossing Rigidity Audit

Status: `PAPER-LEVEL RESEARCH RESULT / AUDITED / NOT FORMALISED IN LEAN`

Release: `v0.3.0`

## Purpose

After S4, the bounded rigidity-first programme asked what a hypothetical
off-line zero or first Suzuki crossing would be forced to satisfy. It did not
reopen the frozen Suzuki implementation programme and admitted no new generic
operator or numerical infrastructure.

## RIG0 result

RIG0 found no objectwise, invariant-preserving map from one prescribed
off-critical zero to a particular Suzuki first-crossing mode. The implication

```text
one bad zero -> not RH -> existence of a first crossing
```

is only existential after the first arrow and loses the chosen zero's quartet,
multiplicity, ordinate, and phase data.

On Suzuki's exact completed source carrier, however, RIG0 proved that for each
earlier radius `0 < b < a0`, the canonical source-orthogonal annular projection
is injective on the full generalized first-crossing kernel.

## RIG1 result

Fix a first crossing `a0`, a shift `sigma < 0`, and `0 < b < a0`. Let `Pi_b`
be the source-inner-product orthogonal projection onto the completed image of
the radius-`b` source space, and let `lambda(b) > 0` be the earlier-radius
ground-form scale. For every vector `u` in the complete generalized
first-crossing kernel, the paper-level theorem
`FirstCrossingKernelQuantitativeAnnularEscape` gives

```text
||(I-Pi_b)u||_sigma^2
  >= lambda(b)/(lambda(b)-sigma) * ||u||_sigma^2.
```

It applies to the whole kernel without assuming simplicity, a chosen vector,
finite-dimensional annulus, or an `L2` representative. It also respects the
even/odd decomposition and implies that the annular restriction is bounded
below and has closed range.

## Derivation

Write `alpha = -sigma > 0`, `m = Pi_b u`, and `n = (I-Pi_b)u`. Source
orthogonality gives `sbar(n,m)=0`, while membership in the complete-form
radical gives, for `q = gbar(m,m)`,

```text
gbar(n,n)=q,
gbar(n,m)=gbar(m,n)=-q,
kbar(n,m)=kbar(m,n)=q/alpha.
```

Crossing positivity gives `q >= 0`. Earlier-radius coercivity and exact
completed zero-extension nesting give

```text
kbar(m,m) <= q/lambda(b).
```

If `q=0`, coercivity forces `m=0` and the estimate is immediate. If `q>0`,
Cauchy--Schwarz for the positive form `kbar` gives

```text
q^2/alpha^2
  = |kbar(n,m)|^2
  <= kbar(n,n)*kbar(m,m),
```

and hence `kbar(n,n) >= q*lambda(b)/alpha^2`. Therefore

```text
||m||_sigma^2 <= q*(lambda(b)+alpha)/lambda(b),
||n||_sigma^2 >= q*(lambda(b)+alpha)/alpha,
```

so `||m||_sigma^2 <= alpha/lambda(b) * ||n||_sigma^2`. The orthogonal norm
split `||u||_sigma^2 = ||m||_sigma^2 + ||n||_sigma^2` yields the released
constant because `lambda(b)+alpha = lambda(b)-sigma`.

The argument takes place in Suzuki's generalized source completion for fixed
`sigma<0`. It does not silently replace that carrier by the original bounded
`L2` kernel, and it uses no pointwise endpoint trace for a generalized mode.

## Limitations and stop decision

This is conditional geometry of a hypothetical crossing, not an exclusion of
one. The constant may collapse as `b` approaches `a0`, and the canonical
annular complement remains uncontrolled and generally infinite-dimensional.
No scalar or uniformly finite-dimensional reduction was obtained.

Therefore RIG1 is recorded as a promotable paper theorem, while RIG2 is not
admitted. No Lean declaration in this release is named
`FirstCrossingKernelQuantitativeAnnularEscape`; the result's evidence is its
audited mathematical derivation, not kernel checking.

## Source

The main mathematical source is Masatoshi Suzuki, *Weil's quadratic form via
the screw function*, [arXiv:2606.09096v2](https://arxiv.org/abs/2606.09096),
especially the projected source carrier, closed-form representation,
continuity and attainment, and the generalized problem in Section 8.5.
