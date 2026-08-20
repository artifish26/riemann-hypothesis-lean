# Lean Experiment Artifact Guidance

The repository root `AGENTS.md` applies. Before editing any experiment in this
tree, also read:

- `EXPERIMENTS/AGENTS.md`;
- `EXPERIMENTS/VERIFICATION_PROTOCOL.md`; and
- the governing experiment plan and report.

An implementation worker may leave a proposed research decision and move the
experiment to `RESULT_READY`, but must not mark it `COMPLETE`, claim that its
Lean target builds, or update aggregate completion wording. A separate
closeout pass must inspect the live diff, rerun every declared focused target
after the last proof edit, scan the changed module for `sorry`, `admit`, and
new `axiom` declarations, and record the result in the report.

If a required build fails, set lifecycle `VERIFYING` and artifact state
`FAILED`. Preserve the mathematical decision only when the compiler failure
does not undermine it.
