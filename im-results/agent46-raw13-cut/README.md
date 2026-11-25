# Canonical raw13 cut

## Scope and source status

Parent: canonical78 raw residual 13, A0=1RB B0=1RC C0=1LA, nine holes. The generic quotient-aware partial cut retains introduced and least-fresh state choices at each authentic query and accounts for all discarded labels via the actual source renaming and blank-delay transport. The generic core was accepted in [CI 45544987354](https://github.com/FlareZ123/bb6/actions/runs/45544987354). The generated cut and ingestion module below must be checked at their current revision before their counts are treated as accepted global coverage.

The exact residual complement is computed by `Agent46CanonicalCut.residuals`, and `Agent46Raw13Ingest.graft_sound` replaces exactly the matched raw13 table in a source-rooted roster. `cover_at_target` consumes the retained quotient-compatible obligations at any target B≥7014. The one-hole #754 cylinder is explicitly retained by `oneHole754_retained`. No timeout is treated as a proof.

## Two complete four-hole branch candidates

### D1 = 0LE

`1RB1LC_1RC0LD_1LA0RB_1LB0LE_------_------` is a strict raw13 residual with four holes. For its sole hard leaf in the complete selected search, `1RB1LC_1RC0LD_1LA0RB_1LB0LE_0RF---_1RE0RB`, the E/1 transition is never queried. [Agent46Raw13Pump0LE.lean](Agent46Raw13Pump0LE.lean) gives an exact two-phase arbitrary-width sweep proof.

Use the source zipper convention (current cell is the head of the left list), T=10, P=01 and Q=11. After 22 steps the authentic run reaches E([],0,3), where E(z,a,b) has state E, left z and right 00 T^a Q^b. For z=[] or [0]:
- E(z,a,b+2) → E([0],a+2,b) in 8a+16 steps.
- E(z,a,1) → B([0],1,a+1) in 8a+16 steps, where B(z,c,d) has state B and right T^c Q^d 1.
- B(z,c,d+1) → B([],c+2,d) in 4c+6 steps.
- B(z,c,0) → E([],0,c+2) in 4c+11 steps.

Consequently F(k)=E([],0,2k+1) reaches F(2k+2) in exactly 24k²+68k+49 primitive transitions, for every k≥0. The blank seed is F(1); induction gives arbitrarily long live prefixes, hence nonhalting for every completion of the E/1 hole. The growth, positive-cost and closed-cost lemmas were kernel-checked locally on Lean 4.36.0-rc2 with the exact copied zipper and sweep definitions, with only propext and Quot.sound. The original-source `never_of_growth` bridge and generated cover still require the actual import closure.

A full deterministic candidate enumeration of the four-hole parent finds 46 split queries, 60 state-mask leaves, 532 cycle leaves, 253 last-hole leaves, 213 n-gram leaves and the one above pumping leaf. The maximum query step in the finite part is 93. `select_complete.cpp` and `generate.py` generate the exact subtree and its proof data using existing checkers. This covers 25^4 literal completions of that canonical parent, with a factor 6 for the original-label fresh-state multiplicities. No external holdout catalogue is used.

### D1 = 1RE

For the hard leaf `1RB1LC_1RC0LD_1LA0RB_1LB1RE_1RF1RC_---0RE`, define A(k) with state A, empty left list and right Q^k 1; E(a,b) with state E, left P and right T^a Q^b; B(a,b) with state B, empty left list and right T^a Q^b 1. Exact sweeps give:

- A(k+1) → E(0,k+1) in 3 steps.
- E(a,b+2) → E(a+2,b) in 4a+10 steps; E(a,1) → B(1,a+1) in 4a+10 steps.
- B(a,b+1) → B(a+2,b) in 4a+6 steps; B(a,0) → A(a+2) in 4a+8 steps.

Writing F(k)=A(2k+1), the blank seed F(1) occurs at step 19, and the growth is F(k) → F(2k+2) in exactly 20k²+58k+43 primitive steps. [Agent46Raw13Pump1RE2.lean](Agent46Raw13Pump1RE2.lean) gives the inductive proof; local checking of growth, cost and positivity against the copied definitions uses only propext and Quot.sound. The source bridge is pending.

The other hard leaf `1RB1LC_1RC0LD_1LA0RB_1LB1RE_0RF0RA_---0RD` closes under a sparse width-14 n-gram invariant (1405 states, 88 left and 448 right edges). Reuse Agent47's source checker and generic trie emitter, whose core checker compiled in run 45555732599 before its raw111-specific row proof job was interrupted. The concrete raw13 certificate remains to be source checked.

The complete candidate for the D1=1RE four-hole parent has 85 splits, 140 state masks, 936 cycles, 495 last-hole leaves, 383 dense n-gram leaves, one sparse n-gram leaf and the one pumping leaf. Maximum finite query step is 203. Its original-label mass is another 6×25^4.

## D1 = 0RE: five uniform all-time sweep certificates

For the four-hole parent `1RB1LC_1RC0LD_1LA0RB_1LB0RE_------_------`, the six difficult one-hole descendants include five whose authentic blank runs enter the same configuration family at step 19: A scans a blank immediately left of an odd contiguous run of ones of length 7. Define F(k) = (A, [], 1(11)^k) in the source zipper convention. All five leave F/0 unassigned.

| Variant | E0, E1, F1 | Exact recurrence for k≥1 |
|---|---|---|
| 0 | 0RF, 1RD, 0RE | F(k) → F(k+2), cost 8k+13 |
| 1 | 1RF, 1RD, 0RE | F(k) → F(k+3), cost 8k+19 |
| 2 | 1RF, 0RA, 0RE | F(k) → F(k+3), cost 10k+17 |
| 3 | 1RF, 1RD, 1LE | F(k) → F(k+3), cost 8k+21 |
| 4 | 1RE, 0RF, 0RA | F(k) → F(k+3), cost 10k+17 |

[Agent46Raw13Pump0RE.lean](Agent46Raw13Pump0RE.lean) proves the five exact block recurrences using arbitrary untouched tails and shared B/C and A/C sweeps. The local Lean 4.36.0-rc2 preflight of the recurrence and authentic-seed orbit uses exact copied `run0`, `join0`, `sweepL`, `sweepR` and `rotate` bodies from `SweepPumping`; the exported orbit-step, seed and positivity theorems have only propext and Quot.sound. The actual `never_of_growth` bridge is submitted for a focused original-source check; no source acceptance is claimed yet.

The sixth hard descendant `1RB1LC1RC0LD1LA0RB1LB0RE1RD1RF---1RD` first queries F/0 at primitive step 21268 in a literal simulator. It cannot be accepted as a last-hole leaf at 7014. A weighted larger-bound certificate is required, including the exact delay/final-query convention. A complete candidate enumeration with the dense n-gram checker up to width 7 found 60 splits, 609 translated cycles, 80 state masks, 339 earlier last-hole leaves, 347 dense n-gram leaves, and the six hard leaves. The entire D1=0RE parent is still retained pending the mixed-bound consumer and original-source checks.

## Exact complement and consuming theorem

The updated candidate census has 353 split queries, 2708 cycles, 948 state masks, 999 last-hole leaves, 15 initial and 826 selected dense n-gram leaves, one sparse n-gram leaf, three original and six additional pumping leaves, and 1722 unresolved canonical leaves. The raw13 parent has 25^9=3814697265625 literal completions; the computed retained mass is 1725412500150. Before this incarnation's two new four-hole candidates the cut retained 1724 leaves and mass 1725417187650. The two branches therefore remove exactly 4687500 weighted literal completions if the source audit accepts the new cut. The global graft is 78−1+1722=1799 quotient obligations, including the exact surviving complement. The earlier D1=0LE-only revision is queued in [CI 45557634300](https://github.com/FlareZ123/bb6/actions/runs/45557634300).

To reproduce, invoke the existing manual workflow `agent46-raw13-cut.yml` with target `ingest`. It generates the proof data, compiles the original-source import closure, and rejects sorryAx or native_decide in the printed profiles. A failed source check leaves the parent obligation intact. The canonical raw13 parent is still open, #754 remains open, and no BB(6) upper bound follows without the remaining covers at the exact attained score.
