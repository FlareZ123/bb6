# Agent 32: independent review of residual symmetry and root-map diagnostics

**Date:** 2026-11-16 10:15 UTC

I independently checked the Python transform in canonicalize_residual_frontier.py against the exact Lean action normalizedTable e mirror m = renameTable e (if mirror then reflectTable m else m) in Symmetry.lean.

The actions agree:

- old state q maps to pi(q), with pi(A)=A and pi any permutation of B–F;
- the input symbol is unchanged;
- the output write bit is unchanged;
- the output direction is XORed with the reflection bit;
- the successor state maps to pi(q');
- the root blank configuration is fixed because A is fixed and the all-zero tape/head-at-zero configuration is reflection invariant.

I independently enumerated the 240 transforms in executable JavaScript. It reproduced both records:
- Machine C: 00:M101;10:M112;20:M110;21:M011, orbit 40, stabilizer 6; canonicalizer chooses identity state permutation plus reflection.
- #623: 00:M101;10:M002;20:M003;30:M113, orbit 120, stabilizer 2; same canonicalizing transform.

No semantic mismatch found. Important interpretation: these are orbits of partial-table cylinders, not complete-machine orbit counts. They are descriptive metadata only; do not use orbit sizes to multiply/add raw cylinder masses or infer that the audit tree is symmetry-equivariant. Lean's disjoint terminal accounting remains the authority.

I also reviewed the root-map distinction: both mapped terminals stop at tree depth four; the separate physical probe follows six genuine successful moves and identifies B/1 for Machine C or D/1 for #623. Those are not contradictory stop conditions. For any completion of the four-row leaf, the probe theorem supplies the same six-move raw blank prefix; the next branch obligation is all 25 actions at that slot. A halt there has score 7, so it is outside the current DecidedBelow 6 target.

This is a source-level and independent finite-enumeration review, not a local Lean preflight or CI acceptance. I did not rerun the exporter or modify its workflow. Agent 13 remains the export integration owner.
