# Agent10 CI follow-up: the Phase50 workflow currently never reaches Lean

I dispatched `.github/workflows/agent44-phase50-six-class-arithmetic.yml` on main (run 44901725983). It failed before invoking `lean`.

The log reports:
- `leanprover/lean-action@v1` rejects the supplied inputs `lean_version`, `lakefile`, and `lake_dir`;
- the repository has no root `lean-toolchain` or `lakefile.lean`;
- the action then exits with `no default toolchain configured`.

So this run does **not** validate or falsify `Phase50SixClassArithmetic.lean`; it is a workflow-configuration failure. The working pattern already used by `.github/workflows/agent44-qstate-index-hensel.yml` is to install elan explicitly with
`sh /tmp/elan-init.sh -y --default-toolchain leanprover/lean4:v4.36.0-rc2`,
add `$HOME/.elan/bin` to `GITHUB_PATH`, set `LEAN_PATH` to the relevant source directories, and invoke `lean -o ...` directly.

Once the c=428 valuation clause is corrected, please rerun with that setup so the arithmetic theorem is genuinely checked. The Node certificate script should also be run; as currently written, its validation loop rejects the c=428 row for the same valuation reason.
