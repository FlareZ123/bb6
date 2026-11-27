# Raw11 Extra28: first-hole refinement and binary-counter proofs

Parent: `1RB0LB_1RC1LC_0LA0LD_------_------_------`. The first hole is D1 at step 9. Eight ordinary children close by translated side cycles. D1=0LC has a prior locally checked WeightedBound 42 (3309 nodes); D1=0LD now has a locally kernel-checked WeightedBound 64 (3357 nodes). The ten other ordinary children still require full kernel-checked Covers. This is not a complete Raw11 parent Cover or a global roster reduction.

## Checked D1=0LD result

`BB6.Agent44Extra28LD.cover : Cover (WeightedBound 64) parent`. The exact child is `1RB0LB_1RC1LC_0LA0LD_---0LD_------_------`. The certificate tree has 2839 translated cycles, 371 last-hole leaves, 140 normalized splits, five two-stack automata leaves and two symbolic leaves; maximum ordinary query index 58. The two symbolic leaves share an unbounded binary counter: at E the left tape is zero followed by k copies of 11 and a zero sentinel, and the right tape comprises bits separated by zeros. A carry over one takes two transitions; resetting at zero erases the carry and returns to the least significant bit in 2k+4 steps. Blank entry occurs after 12 steps. The proof uses the actual SweepPumping / zipper transport to NeverHalts, not a finite simulation. Both F0=1LC and F0=1LD variants are checked.

`Raw11Extra28LDRefine.consume` gives a conditional parent Cover at any B>=64, assuming the already established LC child lifted to 64 and the ten remaining exact obligations. `exactCodes` checks their table codes. The remaining D1 moves are 1RB,0RC,1LC,0RD,1LD,1RD,0LE,0RE,1LE,1RE.

An additional original-source checked counter theorem, `BB6.Agent44Counter28RE.never`, closes the prepared leaf `1RB0LB1RC1LC0LA0LD1LF1RE1RD---0RE0LF` from blank entry at step 20; this is not yet a Cover for the whole D1=1RE child.

## Reproduction

`ld-source.tar.gz` contains the generator, both symbolic source modules, the checked refinement, manifest, and hashes of the exact checked generated source. Extract in an empty directory; run `BB6_Q0_AUTOMATA="$PWD/q0-open-automata.cjs" node generate.cjs`, then `sha256sum -c LD-checked.sha256`. Use Lean 4.36.0-rc2 and artifact 15144626755 (exact original source dependency closure), with LEAN_PATH including the working directory and extracted a47-raw11-root52 directory. Compile Raw11Counter28LD, Raw11Counter28RE, Raw11Extra28LDBase, Raw11Extra28LDPart0 through Part4, Raw11Extra28LDJoin and Raw11Extra28LDRefine with lean -o MODULE.olean MODULE.lean. All passed locally, with standard axioms only (propext, Classical.choice, Quot.sound), no sorryAx/native_decide. Local GitHub DNS unavailable; dependencies transferred by artifact and repository writes by connector.

The previous LC certificate remains in source.tar.gz; extract separately, run python generate.py then python split.py, compile Raw11Counter28, Raw11Extra28D1LCBase, Part0..4 and Join, then the separately stored Raw11Extra28Refine.lean. Its checked hashes are in checked.sha256. Both child results use the existing PhaseTree and PhaseFrontier libraries.

## Complete candidate discovery for remaining children (not yet kernel checked)

All ten remaining children now have complete bounded-tree candidate discoveries; all initially open leaves were solved by finite automata except the source-checked RE counter. For D1=0RE one harder leaf `1RB0LB1RC1LC0LA0LD1LF0RE1RD1RA---1LE` requires ngram width 10 (78/84 stack states, 474 reachable rows). Candidate bounds in move order: 1RB 72, 0RC 84, 1LC 101, 0RD 79, 1LD 96, 1RD 119, 0LE 81, 0RE 150, 1LE 141, 1RE 158. Do not claim these bounds until the exact complete trees and parent consumer compile. Next work: shard kernel checks, compose LC and LD plus ten siblings, then consume Extra28 into the exact Raw11 route.
