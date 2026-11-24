# 3-adic symbolic block residues (intermediate result)

This directory records a proof-engineering lemma for the D-regular shift system. It is **not** a closure of the D0 blank-root trajectory and does not change the BB(6) bound.

## Kernel-checked arithmetic

`ThreeAdicQuotientMod.lean` compiles with Lean 4.36.0-rc2. Its audited declarations have only the standard `propext` dependency.

For a regular block of length (k), the D-regular shift has the form

[
  a' = c + 8^k p,qquad D=3^k,
]

where (p) is the input lift quotient and (c) is the small base-run output offset. The next block's lift quotient is

[
  p' = leftlfloor\frac{c+8^k p}{3^k}\right\rfloor.
]

The two lemmas establish:

- ((c+Ap)\bmod D) depends only on (p\bmod D);
- (((c+Ap)/D)\bmod m) depends only on (p\bmod(Dm)).

Taking (A=8^k) and (D=3^k), the second identity is the quotient-residue recurrence needed to propagate a finite 3-adic window across a block. It gives a route to a symbolic block transducer that carries only the residue needed for future base states, rather than repeatedly materializing the enormous unary parameter.

## Root-19 status and blocker

A local Lean 4.36.0-rc2 attempt to compile the final 9,780-step root-19 composition (including the minimal `run_add` composition over `NineteenthBlock3`) reached the 4-GiB cgroup ceiling and was OOM-killed. A direct `fastRun 9780` attempt also exceeded that ceiling. This is a resource failure, not a counterexample or a failed mathematical equality; do not repeat the same compilation unchanged.

A separate 512-step base trace, checked as 512 individual `DRegular.next` transitions, compiled in about 6 seconds with roughly 0.85 GiB peak RSS. That experiment demonstrates that small base traces can be checked cheaply, but it is not yet connected to the authentic root: the first lift requires a high-precision residue of (t_{18}), while the currently exported arithmetic theorem supplies only (t_{18}\bmod 27). The attempted direct proof of (t_{18}\bmod 3^{512}) by kernel reduction also exceeded the local time limit.

## Next useful step

Use the quotient-residue lemma together with the exact source prefix to derive the needed high-precision residue from the earlier root chain, or move the already established terminal composition to a runner with sufficient memory. The missing ingredient is a source-connected high-precision residue certificate; another unchanged full-state compile or another finite scan is not useful.
