# Canonical raw13 cut

## Scope and source status

Parent: canonical78 raw residual 13, A0=1RB B0=1RC C0=1LA, nine holes. The generic quotient-aware partial cut retains introduced and least-fresh state choices at each authentic query and accounts for all discarded labels via the actual source renaming and blank-delay transport. The generic core was accepted in [CI 45544987354](https://github.com/FlareZ123/bb6/actions/runs/45544987354). The generated cut and ingestion module below must be checked at their current revision before their counts are treated as accepted global coverage.

The exact residual complement is computed by `Agent46CanonicalCut.residuals`, and `Agent46Raw13Ingest.graft_sound` replaces exactly the matched raw13 table in a source-rooted roster. `cover_at_target` consumes the retained quotient-compatible obligations at any target B≥21269. The one-hole #754 cylinder is explicitly retained by `oneHole754_retained`. No timeout is treated as a proof.

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

[Agent46Raw13Pump0RE.lean](Agent46Raw13Pump0RE.lean) proves the five exact block recurrences using arbitrary untouched tails and shared B/C and A/C sweeps. The local Lean 4.36.0-rc2 preflight of the recurrence and authentic-seed orbit uses exact copied `run0`, `join0`, `sweepL`, `sweepR` and `rotate` bodies from `SweepPumping`; the exported orbit-step, seed and positivity theorems have only propext and Quot.sound. The full original-source `never_of_growth` bridge passed [CI 45571028030](https://github.com/FlareZ123/bb6/actions/runs/45571028030), revision `68cb30070c6dfa854ef703739daca6d879dc6887`.

The sixth hard descendant `1RB1LC1RC0LD1LA0RB1LB0RE1RD1RF---1RD` first queries F/0 at primitive step 21268 in a literal simulator. It cannot be accepted as a last-hole leaf at 7014. A weighted larger-bound certificate is required, including the exact delay/final-query convention. A complete candidate enumeration with the dense n-gram checker up to width 7 found 60 splits, 609 translated cycles, 80 state masks, 339 earlier last-hole leaves, 347 dense n-gram leaves, and the six hard leaves. The late leaf's exact weighted bound is 21269, including the final query and no incoming blank-preserving delay. [CI 45571477539](https://github.com/FlareZ123/bb6/actions/runs/45571477539) accepted the original source at `225a2a1eb0fb5a9225302184256f440a36bbb16c`. The entire D1=0RE parent, its 60 splits and empty complement, and the weighted compatibility conclusion at 21269 passed [CI 45571630123](https://github.com/FlareZ123/bb6/actions/runs/45571630123) at `98492ef9a51cc393e10edcf32fb23b6d26b12a50`. The global graft audit is separately queued; it is not accepted yet.

## D0 = 0RC: complete five-hole candidate

The parent `1RB1LC_1RC0LD_1LA0RB_0RC---_------_------` has 287 split queries, 4670 translated cycles, 396 state masks, 1340 last-hole leaves, 191 dense n-grams, and one remaining hard leaf. Its exact first query is D/1 at step 10. The hard leaf is `1RB1LC_1RC0LD_1LA0RB_0RC1LE_0LA0LF_1LB---`.

Put F(a,b)=(A, [], 0(10)^a(11)^b1). The genuine seed F(1,0) occurs after 12 primitive transitions. For odd a=2k+1, b>=0, the exact rules are:
- F(2k+1,b+1) → F(2k+3,b), cost 12k+16.
- F(a,0) → F(1,a+1), cost 4a+16.

Thus F(1,b) → F(1,2b+2) with cost 6b²+18b+20. The exact arbitrary-tail sweep inductions, reset, drain, seed, orbit, positivity, and closed cost lemmas passed local Lean 4.36.0-rc2 against the copied source definitions, only propext and Quot.sound. [Agent46Raw13Pump0RC.lean](Agent46Raw13Pump0RC.lean) includes the actual never_of_growth bridge; the full parent proof is submitted under target zeroRC. The complete parent, exact empty complement, and weighted bound 7014 were source-accepted in [CI 45572254080](https://github.com/FlareZ123/bb6/actions/runs/45572254080), pinned revision `a9a20278c7a0cdc541a6d40cdfe58e7af539759b`.

## D0 = 0RD: complete five-hole parent

The five-hole parent `1RB1LC_1RC0LD_1LA0RB_0RD---_------_------` has 158 authentic split queries, 2800 translated-cycle leaves, 176 state masks, 630 last-hole leaves, 20 dense n-gram leaves and five pumping leaves. Its first query is D/1 at step 8.

The new [Agent46CarryPumping.lean](Agent46CarryPumping.lean) proves a generic exact nested-carry induction: if a depth k preparation uses 2k+prep steps and constructs k repeated two-cell blocks plus a marker, and the marker completion costs fin steps, then recursively draining those k blocks from depth zero advances the right counter by one in (prep+fin+2)·2^k−2 steps. The preparation, every lower carry and marker completion are equalities of the actual partial-machine semantics for arbitrary untouched suffixes. The blank-left version has its own exact preparation and marker.

[Agent46Raw13Pump0RD.lean](Agent46Raw13Pump0RD.lean) instantiates the theorem for three of the hard leaves, then uses two ordinary sweep inductions for the remaining two.

| Variant | D1 E0 E1 F0 F1 | Authentic seed | Positive exact recurrence cost |
|---|---|---|---|
| 0 | 1LE 0LF --- 1RD 0LE | E, [], (00)^1 1 after 15 | 8·2^k−2 for k→k+1 |
| 1 | 1LE 1RD 0LF 0LE --- | E, [], (00)^1 1 after 13 | 6·2^k−2 for k→k+1 |
| 2 | 1RE 0RF --- 0LC 0RF | A, [], (11)^2 10 after 32 | 10·2^k−2 for k→k+1 |
| 3 | 1RE 0RB 0RF --- 1RE | E, (01)^1 00, [] after 9 | 4n+17 for n→n+1 |
| 4 | 1RE 0RB 0RF --- 1LD | E, (01)^1 00, [] after 9 | 6n+19 for n→n+1 |

For variants 3,4 the family is E,(01)^(n+1) 00 1^n,[]. The five exact unbounded recurrence proofs and the complete parent with empty complement at weighted bound 7014 passed the original-source [CI 45573192648](https://github.com/FlareZ123/bb6/actions/runs/45573192648) at pinned revision `fb886531bb3364f6cb6c3c0af5806be8dcdb0231`.

## D0=0LC complete five-hole parent

For `1RB1LC1RC0LD1LA0RB0LC---------------`, the first query is D1 at step 10. The candidate tree has 261 splits, 261 halt branches, 4118 translated cycles, 336 state closures, 1314 last-hole bounds, 227 n-gram certificates and five pumping leaves. The weighted bound 7014 and empty complement passed original-source [CI 45589483594](https://github.com/FlareZ123/bb6/actions/runs/45589483594), pinned at `b6a0aefabdc340b1b0cfcb5f2b4ddccd77e60102`. The parent covers 25^5 literal completions, or 3*25^5 in the raw13 mass accounting.

The five difficult leaves have exact growth maps in [Agent46Raw13Pump0LC.lean](Agent46Raw13Pump0LC.lean). All families below have state A and empty left zipper, with the listed right word:

| Variant | Right word | Parameter update | Primitive cost | Blank seed |
| --- | --- | --- | --- | --- |
| 0 | 1^(3(n+2))0 | n+1 | 24n+63 | n=2, t=166 |
| 1 | 1^(2(n+2)) | n+2 | 18n+23 | n=2, t=41 |
| 2 | 111(00111)^(2n+1) | n+1 | 56n+82 | n=0, t=26 |
| 3 | 1^(2(n+2)) | n+2 | 4n+25 | n=1, t=20 |
| 4 | 1^(6n+10) | n+1 | 72n+106 | n=0, t=66 |

Variant 2 uses two exact phases: F(k)=111(00111)^k and G(k)=F(k)001001, with F(k) to G(k) in 14k+22 steps and G(k) to F(k+2) in 14k+32 steps, k>=1. This replaces the width-8 sparse n-gram candidate with an arbitrary-width sweep proof. All five growth identities and blank seeds were locally kernel-checked under Lean 4.36.0-rc2 against exact copied sweep semantics. The manual `zeroLC` target now accepts the actual repository dependency closure and all five never-halting bridges. The global candidate incorporates this independently accepted parent.

## D0=0LB complete five-hole parent

For `1RB1LC1RC0LD1LA0RB0LB---------------`, the first query is D1 at step 13. Candidate census: 244 split queries and halt branches, 3846 translated cycles, 356 state masks, 1352 last-hole bounds, 46 dense n-grams, and nine pumping leaves. Weighted bound 7014 and empty complement passed [CI 45591237923](https://github.com/FlareZ123/bb6/actions/runs/45591237923), pinned at `bac7ea83a8b446200ad727c66d11a474f23ded7d`.

[Agent46Raw13Pump0LB.lean](Agent46Raw13Pump0LB.lean) provides exact macro identities and authentic seeds. All states are A with empty left zipper:

| Variant | Right word | Parameter update | Exact primitive cost | Seed time |
| --- | --- | --- | --- | --- |
| 0 | 111000100100(0100100)^(n+1) | n+1 | 108n+341 | 344 |
| 1 | 1^(2n+3)01 | n+1 | 6n+21 | 11 |
| 2 | 1^(2n+3)01 | n+1 | 10n+21 | 11 |
| 3 | 1^(2n+3)01 | n+2 | 6n+27 | 11 |
| 4 | 1^(2n+5)00000 | n+1 | 36·2^n−2 | 39 |
| 5 | 1110101^(9n+5) | n+1 | 48n+167 | 42 |
| 6 | 1^(8n+3)0101111111 | n+1 | 48n+118 | 66 |
| 7 | 1110^(2n+1)1 | n+3 | 12n+46 | 11 |
| 8 | 111(01)^(n+1) | n+3 | 12n+47 | 11 |

All seeds use n=0. The local copied-source check accepts eight growth equations and variant 4's exact preparation/finish lemmas for the generic nested-carry theorem; the original-source bridge and full parent audit now pass `zeroLB`. Variant 0 transports 7-cell blocks right-to-left in 33 steps and left-to-right in 21 steps, with separate exact final-block boundary. Variant 5 has three phases (48n+52, 44, 71 steps); variant 6 has two (24n+62, 24n+56). No finite simulation horizon is used to justify a nonhalting claim.

## Exact complement and consuming theorem

The updated candidate census has 353 split queries, 2708 cycles, 948 state masks, 999 last-hole leaves, 15 initial and 826 selected dense n-gram leaves, one sparse n-gram leaf, three original and six additional pumping leaves, and 1717 unresolved canonical leaves after replacing D1=0RE and D0=0RC,0RD,0LC,0LB by their standalone bounded parent certificates. The raw13 parent has 25^9=3814697265625 literal completions; the computed retained mass is 1725292968900. Before this incarnation's two new four-hole candidates the cut retained 1724 leaves and mass 1725417187650. The three four-hole and four five-hole closures now add an exact candidate mass removal of 3·6·25^4 + 4·3·25^5 relative to the preceding cut. The 0RE,0RC,0RD,0LC,0LB parent theorems are independently source-accepted; the new global graft requires its own source check. The global graft is 78−1+1717=1794 quotient obligations, including the exact surviving complement. The earlier D1=0LE-only revision was cancelled in [CI 45557634300](https://github.com/FlareZ123/bb6/actions/runs/45557634300); the 0RE-only ingest was also cancelled in [CI 45572030362](https://github.com/FlareZ123/bb6/actions/runs/45572030362). Neither cancellation establishes global acceptance.

To reproduce, invoke the existing manual workflow `agent46-raw13-cut.yml` with target `ingest`. It generates the proof data, compiles the original-source import closure, and rejects sorryAx or native_decide in the printed profiles. A failed source check leaves the parent obligation intact. The canonical raw13 parent is still open, #754 remains open, and no BB(6) upper bound follows without the remaining covers at the exact attained score.
