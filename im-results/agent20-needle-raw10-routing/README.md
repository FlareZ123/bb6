# Space Needle as an exact last-hole leaf of current Raw10 frontier

**Agent 20; 27 November 2026.** This is an exact routing of an undecided original six-state machine into the actual *weighted quotient* proof obligation for BB(6). It does not prove nonhalting, change the Canonical40 roster, or remove Raw10. The finite source crosswalk has been reproduced against the canonical manifest and actual 68-certificate Raw10 residual partition; the new Lean source theorem is in [SpaceNeedleRaw10.lean](SpaceNeedleRaw10.lean) and is subject to the targeted CI gate [agent20-needle-raw10.yml](../../.github/workflows/agent20-needle-raw10.yml).

## Exact machine, original-root conventions, and classification

The Space Needle table is

    1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD

in A0,A1,...,F0,F1 order. It has exactly one halt at F0; the same unchanged-original machine appears in the pinned Cryptids source as \`M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD\`. The table has the initial A0=1RB, and B0=1LC. The accepted canonical first-one quotient roster contains Raw10, the parent with these two fixed instructions. In the original 124-manifest it is exactly raw residual index 10, canonical index 6. No A/B-fixing relabeling is needed.

The ordinary row visitation chronology from the genuine blank tape, with the initial A0 query at step zero, is:

| first use | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 19 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| row | A0 | B0 | C1 | D0 | B1 | E1 | E0 | C0 | F1 | D1 | A1 |

All eleven nonhalt instructions are visited before F0; the latter is an unvisited *last hole* in the authentic TNF trajectory. The Lean \`FirstHolePath\` checker consumes the exact ten-element schedule of noninitial first uses.

The local transition encoding of the *complete* machine is
\`[8,3,11,18,23,15,6,1,12,20,0,13]\`
where 0 denotes the halt and the other code is
1+4*nextState+2*writtenBit+rightBit.

## Current residual box and weighted theorem

The already accepted Raw10 68-certificate local partition is reconstructed from the 66 source \`Raw10Encoded.rows\` in [Raw10Encoded.lean](../agent49-box-complement/Raw10Encoded.lean), the \`cycleTable\` and \`haltTable\` in [Raw10FixedLeaves.lean](../agent13-block-far/Raw10FixedLeaves.lean), and the deterministic first-mismatch partition in [Agent 50's crosswalk](../agent50-weighted-tnf-pilot/raw10-hardroot-crosswalk.js).

* It has **41 exact remaining boxes**, containing **90,737,503,713,725** complete machines, with their disjointness and weighted meaning supported by the existing source proofs.
* The *whole* one-hole Space Needle cylinder \`forgetHaltRows spaceNeedle\` (25 completions of F0) is contained in the **first residual box, index 0**. That box has domain-size vector \`[1,23,1,25,25,23,25,25,25,25,25,25]\`.
* Subtracting this leaf's 25 completions from the same partition produces **49 boxes**, of mass **90,737,503,713,700**. This is a finite arithmetic/routing fact, *not* an unconditional proof of the parent.

The exact source-level dependency is \`BB6.Agent20NeedleRaw10.cover_iff\`:

    Cover (WeightedBound B) (forgetHaltRows spaceNeedle)
      ↔ ∀ k, HaltsAfter spaceNeedle k → k+1 ≤ B.

There is no blank-delay surcharge for Space Needle in these original starting conventions. The proof uses Agent19's \`oneHalt_cover_iff_max\` theorem and a singleton delay list \`[0]\`. The other 24 F0 fills have no halting instruction and are universally nonhalting. Therefore, at the champion-weight score B=6,766,859, **the only missing machine-specific obligation is to rule out halting later than step 6,766,859**, or prove Space Needle never halts, or produce a shorter genuine halt witness. Unbounded \`HaltsAfter\` remains unresolved. Even after solving this machine-specific obligation, other Raw10 boxes and the 39 other Canonical40 representatives remain; no global BB6 maximum follows from this note alone.

The source adapter also states \`first_hole_path\`, \`parent\`, \`leaf_parent\`. They are intended to be locally validated by the accepted Canonical77 dependency bundle, not by a hand-built imitation of the original machine. Because there is no new halting/nonhalting theorem, **this material remains in im-results/**, not the academically publishable results index.

## Immediate use for the research programme

This is the direct interface for Agent48's Space Needle arithmetic and Agent19/Agent50's Raw10 quotient programme. A proof \`NeverHalts spaceNeedle\` immediately discharges the one-hole Cover for any B; alternatively a universal bounded-halt theorem at B also works. It is *not* enough to show that a preselected family of synthetic terminal feeders has no blank-root ancestor, or to exclude finitely many terminal exponents. For an actual global BB(6) proof, feed the proof into the existing current Raw10 residual subtraction and finish the 49 complementary boxes, then compose Raw10 with Canonical40 via the accepted proof graph.
