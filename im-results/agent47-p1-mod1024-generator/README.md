# Agent 47: reusable original-source P1 modulo-1024 certificate generator

Research status 2026-11-02: **intermediate computational/proof-generation infrastructure**, with source-level verification pending for the complete 36-family batch. Two families, residues 14 and 62, have already passed separate full-original-source kernel CI [41508096971](https://github.com/FlareZ123/bb6/actions/runs/41508096971) and [41509337455](https://github.com/FlareZ123/bb6/actions/runs/41509337455), respectively.

## What is in this directory

`P1Mod1024Generator.tar.gz.b64` is a reproducibly archived set of five source files:

- `p1_scan_mod1024.py`: exact-Integer symbolic inverse traversal of the original P1 `G` source, using affine triples `a*w+b*q+c`, `w=2^(1024q)`. The 36 candidate residue families were earlier discovered **computationally by Agent 28**, particularly its `im-results/agent28-p1-mod1024/README.md`; source code reconstructed and adapted with that explicit attribution.
- `gen_p1_mod1024.py`: deterministic `Affine` Lean source enumerating every GAncestor, `Blocked` proof tree, gap source, and authentic blank-entry final theorem for each residue. Uses atomic, locked file writes.
- `P1GapTemplate.txt`: a uniform Lean proof excluding all terminal 14-power leaves using a coefficient band, relying on `Nat.pow_lt_pow_iff_right`, `omega`, and exact exponent identities.
- `P1FinalTemplate.txt`: connects the `Blocked` proof to Agent50's original-source critical-gateway theorem `critical_target_implies_three`.
- `verify_batch.py`: six-shard runner whose each shard emits, source-compiles, and audits six of the 36 complete parametric residue proofs.

The archive is 6920 base64 characters, gzipped tar sha256 `b883ac81e8ed66a686cf078578d73d9769fe685c3c4269d7cc7b4e09ff3923e4`. The member file hashes are checked by `.github/workflows/agent47-p1-mod1024-batch.yml` before any dynamic generation. The workflow is manual dispatch or narrowly guarded issue-created only, not per-commit.

## Mathematical scheme

For each candidate residue `r≡14(mod16)`, `14≤r≤1006`, write
```
n=1024*q+r
w(q)=2^(1024*q)
M_r=7*2^(r-10)
u_r(q)=M_r*w(q)-q.
```
Then `H(n)-6 = 2048*u_r(q)-2*r-16`. Every node in its exact inverse cone reduces to affine expressions in `u_r(q)`; the generator enumerates a complete finite tree using Agent47's original-source exact `inverseAt` enumeration and proves all branches through the inductive sound `Blocked` kernel. Its power leaves are `A*u_r(q)-C` with strict coefficient bounds `1024<A<2048`. The elementary exponential-vs-affine lower bound `u_r(q)≥(M_r-1)q+M_r` places each strictly between `14*2^(n-1)` and `14*2^n`, proving no `14*2^j` equality for any j.

Agent28's earlier computational listing found **36 exact-affine closed residue classes** among the 64 congruent 14 modulo16. Our reimplemented exact symbolic scan independently reproduced that inventory with 16 cones of 11 hubs, 16 cones of 15 hubs, and four cones of 19 hubs, totaling 492 hubs, 1476 positive inverse branches, and 984 excluded terminal branches. This census is still computational until the complete batch workflow succeeds.

The 36 candidate residues are:

```
14, 62, 94, 110, 158, 190, 206, 254, 302, 366, 414, 430,
446, 462, 478, 510, 558, 622, 638, 654, 670, 686, 702, 718,
734, 782, 798, 846, 862, 878, 894, 910, 926, 958, 974, 1006.
```

The other 28 residue classes fail this simple affine inverse closure and require different proof mechanisms. The certified subclasses do not establish a blank-start P1 nonhalting result or BB(6)'s exact value.

## Validation

Local mock-signature compile tests: r=14,62,94,510,1006 generated; all gap proof modules (including r510 and r1006 with ~150-300-digit constants) compiled with Lean 4.36.0-rc2, and full Affine/Blocked/Final modules for r94,510,1006 passed against signature-matching mocks. **Such local mocks are never acceptable as decisive mathematical certification.** The six-job full original-source [CI run 41511025824](https://github.com/FlareZ123/bb6/actions/runs/41511025824) is the required next verification stage, triggered by [issue #4](https://github.com/FlareZ123/bb6/issues/4). Publish the 36-family claim in `results/` only if every job and all its final theorem axiom audits pass.
