# Machine #429: a two-parameter odd/even C/0 corridor

**Intermediate mathematical theorem, 9 November 2026.** Lean 4.36.0-rc2 locally kernel-checked the exact source-shaped six-state machine's transition, sharp primitive head maximum, and complete C/0 count. The authentic blank-run reachability of this prepared input family is **not known**; the result does **not** decide #429 or BB(6). The local imported baseline was copied from the existing exact machine table and monitor definitions. Independent unchanged-repository-import CI is a separate audit obligation.

## The complete symbolic transition

Use the exact nearest-first original source zipper (state 2 = C), with the Boolean left stack nearest first and the right stack empty. For arbitrary natural numbers k,j and arbitrary finite untouched left suffix T, let

    P(k,j,T) = C/0, left = 1^(2k+3) 010 1^(2j) 0 T, right = blank.

The proof in [BB429OddEvenCorridor.lean.xz.b64](BB429OddEvenCorridor.lean.xz.b64) establishes an identity of complete zipper configurations:

    run(4k+4j+25, P(k,j,T))
        = C/0, left = 10 1^(2k+2j+8) T, right = blank.

The exact primitive instruction count is 4k+4j+25, with no bounded parameter search. This family has an odd initial block and arbitrarily many marked cells in the intermediate even block. It complements Agent 1's [even-initial-block contextual return](../agent1-429-w4-boundary/CZeroContext.lean) and [odd-initial-block, three-blank fatal branch](../agent1-429-w4-boundary/CZeroContext.lean).

## Stronger primitive-trajectory certificates

[BB429OddEvenCorridorMax.lean.xz.b64](BB429OddEvenCorridorMax.lean.xz.b64) proves

    runWithMax(4k+4j+25, P(k,j,T))
        = (endpoint, signed displacement +3, maximum displacement +3).

Here runWithMax is Agent 1's exact monitor of **all primitive head positions**, starting with initial relative head zero. The maximum of +3 is sharp, attained at the endpoint. Thus every intermediate primitive head lies at or to the left of the final head, independent of both unbounded parameters and arbitrary T.

[BB429OddEvenCorridorCount.lean.xz.b64](BB429OddEvenCorridorCount.lean.xz.b64) further proves

    runCount(4k+4j+25, P(k,j,T))
        = (endpoint, 1).

The monitor counts C/0 at instruction starts, excluding the terminal configuration. Consequently there are **exactly two C/0 visits in the closed corridor**, at its beginning and end; no other C/0 can occur within. Both have completely blank right tapes. This establishes a *safe, fresh-right C/0-to-C/0 corridor*: any raw original-machine configuration faithfully represented by P and already at the global right-head record extends that record by precisely three cells without entering the fatal C/0-with-marked-right gate during the corridor. Source-level representation and the raw bridge are existing infrastructure; this last sentence is a mathematical corollary conditional on the represented input and its prior record property.

These are infinitely parametrized whole-tape theorems. They are **not** a global invariant on all blank-origin configurations. The currently observed authentic C/0 left-stack pattern is broader and includes shapes outside P; a proof that every genuine C/0 lies in a closed collection of such corridors, or a genuine halt witness, remains missing.

## Reproducibility

The three compressed source files are restored with [restore.py](restore.py), an atomic, lock-protected decompressor with SHA-256 checking. Run it with Python 3 and compile the Lean sources with Lean 4.36.0-rc2. The dependencies are existing original repository modules BB429OddExcursion and W4HeadMax. The count module defines an identical source-level C/0 monitor to the existing W4CZeroCount to avoid its unrelated import graph. All local proofs checked **without sorry**; the axiom audits were:

- BB429OddEvenCorridor.odd_even_corridor: [propext, Quot.sound].
- BB429OddEvenCorridorMax.odd_even_corridor_max: [propext, Classical.choice, Quot.sound].
- BB429OddEvenCorridorCount.odd_even_corridor_count: [propext, Classical.choice, Quot.sound].

The locally compiled test module for BB429OddExcursion repeated its original published action table and the one unbounded AF-pair lemma, and the local head/count monitors repeated the previously published source definitions. This is strong source-shaped Lean evidence, though **not yet a source-imported CI certificate**. The local test independently checked k=0..4, j=0..4 with the literal six-state raw-table simulator. The source hashes used in this report are:

| Restored file | SHA-256 |
| --- | --- |
| BB429OddEvenCorridor.lean | 524d8046bea7a051f406aed4192af8f89b087904f74ba2b3d1b6b3b53b530061 |
| BB429OddEvenCorridorMax.lean | 59d8fa26979247b7e37dd91054eacd3d2c4242c88ed57a55bd236967674ee5e5 |
| BB429OddEvenCorridorCount.lean | 5b52cb2e03f037c33a3a233ea431e6d1129f692a949b578dbcc923b65b404a95 |

## Next high-value question

Develop a **closed** all-time language of original blank-reachable C/0 head-record configurations by composing first-event returns over the actual nonlocal tape, not just synthetic local cylinders. The observed authentic left grammar has long odd 1-runs and often chains of isolated 1s before a final even run; this theorem handles only a specific short bridge with an even intermediate run and an explicit second 0. The gap is authentic coverage, not additional finite simulation of the family.
