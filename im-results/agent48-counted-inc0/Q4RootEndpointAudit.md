# TM63 q4 root endpoint: full marked-set audit

## Result

The exact 332-step replay from the kernel-certified initial S1 root state
matches the proposed canonical q4 target on the **entire marked-cell set**,
not merely on count and support.

```
start:  state 3, head 29,
        s1Config 3 7 2 6 0 63 29
steps:  332
end:    state 3, head 223
        s1Config 3 6 1 71 (2^63-1) 0 223
marks:  106
support: [-10,232]
symmetric difference between replay and target: 0
```

The initial S1 encoder support was independently compared against the
existing `InitialS1RootWitness.md` list of 225 marks; the two initial sets
are equal. The replay uses the twelve exact `tm2` rows in
`ChampionRootBridge.lean` and the exact `d0`, `d1`, `markerWord`,
`lh`, `binDec`, and S1 left/right stream definitions in `S1Encoder.lean`.
It stores the complete set of marked integer coordinates, with all
unlisted cells blank. There is no fixed-window truncation.

## Exact endpoint set

The common marked-cell set, sorted by absolute coordinate, is:

```
[-10, -9, -8, -6, -5, -4, -1, 2, 3, 4, 5, 8, 10, 11, 12, 13, 14,
 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
 31, 32, 33, 34, 35, 38, 41, 44, 47, 50, 53, 56, 59, 62, 65, 68,
 71, 74, 77, 80, 83, 86, 89, 92, 95, 98, 101, 104, 107, 110, 113,
 116, 119, 122, 125, 128, 131, 134, 137, 140, 143, 146, 149, 152,
 155, 158, 161, 164, 167, 170, 173, 176, 179, 182, 185, 188, 191,
 194, 197, 200, 203, 206, 209, 212, 215, 218, 221, 225, 226, 227,
 230, 231, 232]
```

Thus the full replay set equals the full canonical encoder set exactly:
`actual \ target = ∅` and `target \ actual = ∅`.

## Lean finite certificate

`Q4FiniteAudit.lean` now reuses the repository's actual `tm2`,
`fRun`, and `initialS1Finite` declarations from
`ChampionRootBridge` and `InitialS1RootFinite`. It proves the exact
332-step finite replay to the explicit ordered output list and then
proves, order-independently, that this list has exactly the 106 cells
above. The proof body was preflighted in Lean 4.36.0-rc2 against the
identical finite simulator and initial/target lists; its axiom report was
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

The manual-only workflow `.github/workflows/agent48-champion-root.yml`
now copies and compiles `InitialS1RootFinite.lean` and
`Q4FiniteAudit.lean`, then checks both theorem axiom reports and fails
closed on `sorryAx`. The actual imported repository workflow has not yet
run for this addition.

## Reproduction

Run:

```bash
python im-results/agent48-counted-inc0/q4_root_endpoint_audit.py
```

The script asserts the initial-set identity, exact endpoint state/head,
mark count, support, and zero symmetric difference. It also prints the
last ten transitions for a local trace check.

## Proof boundary

This is a reproducible finite computation using the exact original TM63
table and canonical encoder definitions. It closes Agent 24's requested
full-set consistency check, but it is **not** a Lean theorem that the
332-step run reaches the target, and it does not validate the quantified
`oddRst2_q4_counted_source` proof candidate. The source-level q4
composition, the S1 decrement/drain chain, and the final halting score
still require their own successful Lean source audits. Keep this result
in `im-results/`.
