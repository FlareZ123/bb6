# D0=1LF ordinary regions: independent source certificates

## Current result (2026-11-28 17:12 UTC)

The existing conditional nine-split spine has passed original-source CI
(run 46151793808, artifact 15265739265). Leaf 2265 is already unconditionally
source accepted. This work discharges 150 of its 206 ordinary-region
obligations, each with a literal-table Lean theorem
`BB6.Agent3D0LF1Ordinary.coverR<i>` of type
`Cover (WeightedBound 148142) pR<i>`.

Selection: all plan regions with at most 600 nodes before the saved grafts.
150 regions, 12,150 original nodes; 188 original open leaves, including
one 24-way saved graft; 182 Block-FAR proofs after grafting. Every one of
the 196 generated source modules (46 Block-FAR, 150 tree) compiled with Lean
4.36.0-rc2 in 134.47 seconds on four local workers, using the actual
original-source compiled dependency closure from artifact 15175093456.
All 150 Cover axiom audits reported only the standard Lean axioms.
This is local kernel acceptance with original compiled imports, not a
new full-source CI run or a complete parent theorem.

The replay partition reproduced the exact SHA256
`ccfb2890cd09d3d41a79b30d58ab46f8407bc9aa721447c5ad3a49522f592bfb`.
The independent region generator uses the saved census rather than
rediscovering witnesses. Crucial correction: saved one-split graft
children are indexed by **numeric transition code**; the ordinary
tree/Lean byMove order is write, direction, next state. The generator
explicitly permutes the children. In particular, graft 2237 failed
under naive zip and all eight block witnesses passed under numeric
indexing. Lean checks every exact graft, so a wrong order cannot
silently certify a false result.

Reproduce from the repository root:
```sh
P=im-results/agent3-raw139-e1-zeroRD
g++ -O3 -std=c++17 im-results/agent48-raw139-e0-0re/replay.cpp -o /tmp/d0lf1-replay
/tmp/d0lf1-replay 100 2 7 24 11 24 14 24 22 16 24 13 24 24 > /tmp/d0lf1-partition.json
# plan: existing artifact 15265488529, or regenerate with plan-two-exception-spine.py
PYTHONPATH=im-results/agent48-raw139-f1-oneRA python3 "$P/emit-d0lf1-regions.py" /tmp/d0lf1-partition.json /tmp/raw139-d0lf1-spine.json "$P/census-d0lf1.json" /tmp/d0lf1-regions --regions small:600 --cap 600
# Compile D0LF1R<i>.lean roots against original PackedPrefixAudit,
# BlockFAR2, BlockFARBridge and their exact source dependencies.
```

The remaining 56 ordinary regions contain most of the original tree
mass; width-four BFAR and four long late traces require their existing
specialized adapters. No claim that all ordinary regions, the F067
exception, this Raw139 parent, or BB(6) are solved. Continue by extending
the generator for those cases and joining the conditional spine.
