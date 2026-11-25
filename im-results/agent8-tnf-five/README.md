# Five-hole weighted TNF certificates: raw69, raw73, raw78, raw80

Four disjoint cylinders from the authentic 124-entry first-one residual roster.

| Raw | B1 | Candidate exact weighted maximum | Splits | Last-hole | Side-cycle | FAR | Symbolic |
|---|---|---:|---:|---:|---:|---:|---:|
| 69 | 0LC | 88 | 712 | 1887 | 14203 | 286 | 1 |
| 73 | 0LD | 367 | 599 | 1929 | 11624 | 225 | 0 |
| 78 | 0RE | 183 | 860 | 2955 | 16423 | 402 | 1 |
| 80 | 1RE | 164 | 916 | 3163 | 17511 | 395 | 0 |

Each covers 25^5 = 9,765,625 compatible completions. The four weighted maxima include the last halt query and incoming blank delay. Witness tables and exact traces are in generate.py.

Raw69's remaining open leaf 1RB---_1RC0LC_0RD0LF_1LD1RE_0RA0LB_1LB1RA enters A(1,[]) at step 42. With P=01011, A(k,R) has left zipper 0 P^k 1 and right R. The return A(k,[]) to A(k+1,[]) costs 28*2^k-13. An arbitrary-tail recursive resolver proves the exponential macro by induction, not by bounded simulation. Raw78's remaining leaf 1RB1LB_1RC0RE_0RD1RA_1LD1RE_1LF0LB_0LA--- enters a family at step 111, with 12n+10 ones. Three composed sweep phases add 12 ones in 372n+473 steps. Both universal recurrence proofs passed local Lean 4.36.0-rc2 on the copied zipper definitions and join lemma. The Never modules connect them to the existing original-source never_of_growth theorem; original-source build remains pending.

Run python generate.py 69 73 78 80. The generator reproduces exact roster hashes, reconstructs FAR masks, imports the two exact symbolic theorems, and emits chunked audits. Run python replay.py RAW to independently replay the finite partition, side cycles, automata closures and attained weighted bound; for 69 and 78 it explicitly identifies the single symbolic obligation checked by Lean rather than claiming that a finite replay proves it. FiveSiblingRoster.lean proposes projection of all four keys from the original roster (124 to 120) with unchanged bound 395 on the closed part.

**Status:** no global upper bound or BB(6) solution claimed. Original-source Lean compilation and roster projection pending.
