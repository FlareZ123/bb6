# Raw139 E0=1RD — both exceptional leaves closed locally

This is the normalized depth-2 sibling with move `⟨true,true,3⟩` of `BB6.Agent6Raw139Normalized.remainingRows`: `1RB---_1RC---_1LD---_---0LE_1RD1RC_------` (codes `[7,24,11,24,14,24,24,16,15,11,24,24]`). It has six holes. **Both exceptional leaves have locally kernel-checked theorems against the accepted coverage core. The finite parent assembly remains open.**

## Candidate partition

`reproduce.py` applies the existing Agent6/48 search mechanism (C++ exact bounded prefix, ordinary-move splits, candidate side cycles, small FAR, then block-FAR). Its 250-step first pass gives 26,980 splits and 620,541 leaves: 429,405 side cycles, 128,403 last-hole queries, 55,075 FAR witnesses and 7,658 initially open leaves. The second pass gives 7,592 block-FAR candidates, 54 late queries, 10 cycles and two exceptional leaves, now proved individually. One late query has two holes; its 24 ordinary children yield 22 block-FAR and two late last-hole candidates. Every halt-at-split case remains part of the future weighted audit. Counts and checksums are candidate-search evidence, not trusted certificates.

The two exceptional tables, each with only F0 unspecified, are:

- 2959: `1RB1LB_1RC1LF_1LD1RE_1LA0LE_1RD1RC_---0LA`; exact first F0 query at 94,323,044, weighted Cover at 94,323,050.
- 4267: `1RB0LC_1RC1RA_1LD0RB_1LF0LE_1RD1RC_---0LA`; every completion is nonhalting by a wide-block inductive invariant.

## Compact recurrence for 2959

Use a B section with an empty left stack (scanned blank) and right stack `1^n`. Blank entry is at step 10 with n=4. The following sweep identities are proved in Lean in `E0OneRDLate.lean` (reconstruct with `python unpack.py`):

- Even n: return with n+3 ones in 4n+6 steps.
- Odd n: in n+3 steps enter A with n+2 ones on its left and a single one on its right. Each group of three left ones converts into right block 011 in three steps. Write n+2=3k+r. For r=2, two further steps query F0, with empty left and right 11(011)^k1. For r=1, one step gives B with right 1(011)^k1. For r=0 and k≥2, 18 steps give B with right 1^8(011)^(k−2)1.
- B with right 1^m(011)^k1, k>0, returns with right 1^(m+5)(011)^(k−1)1 in 4m+6+6(m mod 2) steps.

The recurrence reaches F0 with final odd n=12,285 and k=4,095. `BB6.Agent1Raw139E0OneRDLate.first_query` proves the exact 94,323,044-step first query using 28 macro sections and parametric sweeps, without evaluating the full raw trace. `BB6.Agent1Raw139E0OneRDLate.weighted : Cover (WeightedBound 94323050) p` applies the existing last-hole weighted certificate. Locally compiled under Lean 4.36.0-rc2 against the accepted E0=0RD core (artifact 15127060543) and the original SparseZipper, SweepPumping, ZipAuditCore sources from Raw58 artifact 15090715339. First-query axioms `[propext, Quot.sound]`; weighted theorem `[propext, Classical.choice, Quot.sound]`. Full source-closure acceptance in the shared gate and E0=1RD parent audit remain outstanding.


## Eight-cell block invariant for 4267

The exact table codes are `[7,8,11,3,14,5,22,16,15,11,24,0]`. The mirror of this table has a forward block-FAR invariant with width 8, cap 1, modulus 2, three most recent block symbols and phase tracking. The untrusted saturation has 729 left states, 2,385 right nodes and 4,102 edges; right-node bisimulation refinement yields 1,312 nodes (including a dead node), 2,444 edges, one accepting zero state and 1,326 active control entries. The new `WideBlock.lean` reuses the actual BlockFAR primitive semantics and proves positive finite exits for all exterior block words. `WideSparse.lean` checks only present rows and proves that absent rows cannot be selected; it derives the inductive invariant and all-time primitive execution. Every finite check is kernel reduction (`decide +kernel`). Reflection and literal-table equality use the existing coverage bridge.

`BB6.Agent1WideBlock.E0OneRD4267.never (m) (hm : compatible ctr m) : NeverHalts m` compiled locally on Lean 4.36.0-rc2 against the accepted E0=0RD core (artifact 15127060543), with axiom profile `[propext, Classical.choice, Quot.sound]`. The exact-table equality uses only `[propext, Quot.sound]`.

Reproduce the wide proof by extracting `wide-source.tar.gz` (SHA256 `2f87d4b70535ff1de36b5f7ebe6cd358c7b535e172c681fbf5f575ad8175eddc`) into a Lean source directory with the accepted BlockFARBridge/FastThreeHoleAudit closure on LEAN_PATH, then run:

```sh
python emit_wide.py
lean -o WideBlock.olean WideBlock.lean
lean -o WideSparse.olean WideSparse.lean
lean -o E0OneRD4267Packed.olean E0OneRD4267Packed.lean
lean -o E0OneRD4267Proof.olean E0OneRD4267Proof.lean
```

Generated Packed/Proof source SHA256: `62fc152d38f0ae0741cf97e142441ad68928bebfeacf45ff9d5bc8e360ef2762`, `b49e31cbe1b9fb32d8f361140206b1bf63d9d2bd6334f7d68806d907772c4f26`. Search and minimization are untrusted; the Lean proof does not rely on these checksums or the search's completeness claims. The remaining work is the checked first-query partition covering the entire six-hole cylinder, including halt-at-split edges, and its original-source gate. No global Canonical64 roster change is justified yet.
