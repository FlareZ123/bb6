# Box27 five-hole slice: complete candidate partition

2026-11-27, Agent49. **Candidate, not yet source-verified.** For D0=14, D1=17, E0=21, root `[8,-1,11,-1,13,13,14,17,21,-1,-1,-1]`, exact first-hole discovery closes all 25^5 = 9,765,625 completions. Proposed weighted bound 108, attained by `[8,4,11,24,13,13,14,17,21,15,3,0]` (107 live moves, zero incoming delay).

| leaf type | count | completion mass |
|---|---:|---:|
| halt | 101 | 432725 |
| side cycle | 1959 | 9321375 |
| last hole | 324 | 8100 |
| two-sided finite stack invariant | 41 | 3425 |
| open | 0 | 0 |

`generate_slice.py` deterministically regenerates the candidate and emits independent Lean chunks. `Box27SliceCore.lean` uses existing source-level Box17 terminal and Agent4 finite-stack checkers, splits all 25 alternatives, and connects the root to raw10Remainder[27]. No finite simulation limit is trusted by Lean. The 41 automata supplant the older symbolic-only seed census. Largest joint invariant: 97 states. Local Lean is available but local GitHub checkout DNS is unavailable; original-source verification is required in CI.

Broader D0=14,D1=17 slice: candidate scan of 244,140,625 completions, 8 open cylinders (mass 200), of which 3 subsequently have lag-XOR finite-stack candidates; 5 still require work. No claim of closure for this broader slice or Box27. The [masked-counter proof](MASKED-COUNTER.md) supplies two further exact one-hole nonhalting arguments, with the original-source audit still required; candidate discovery sets are not assumed identical.

## Earlier single-cylinder investigation

# Raw10 Box27: growing unary-block cylinder

**Mathematical result (paper proof; original-source Lean audit not yet accepted).** All completions of the sparse row

```
[8,3,11,2,13,13,14,17,21,?,3,?]
1RB1LA_1LC0RA_0LD0LD_0RD0LE_0LF???_1LA???
```

are nonhalting. Code 0 is halt; code 1+4q+2w+r is the ordinary transition, r=1 right. Slots are A0,A1,...,F1. Both E1 and F1 are arbitrary (625 raw completions). This is an actual blank-orbit result, not an assertion about prepared-tape reachability.

The source base34 Box27 fixes A0=8, B0=11, C0=C1=13 and permits D0=14. The cylinder is therefore inside that original rectangle, with D1=17, E0=21, F0=3, A1=3, B1=2. It does not close the entire rectangle or the Raw10 parent.

## Exact recurrence

At time 5 the blank-start execution reaches D scanning the rightmost 1 at position 1. The right half-line is blank, and the left half-line is two zeros followed by a block of k=0 ones and then blanks. Denote that configuration R(k) for general k, with D scanning 1.

- D1, E0, F0 take three steps. The scanned marker is erased; cell -1 becomes 1; A scans cell -2. The k old ones occupy cells -2 through -(k+1), with the empty range understood when k=0.
- A1 takes k leftward steps across the old block without alteration; A0 writes the next blank at -(k+2) and moves right to B. B now scans the first of k+1 consecutive ones.
- Each of the first k ones is passed in three moves: B1 erases the current one and moves right into A scanning another one; A1 moves back; A0 restores the erased cell and returns right to B. After k repetitions, B scans cell -1 and the left block has length k+1.
- Six more steps B1,A0,B0,C1,D0,D0 erase the temporary one, restore the rightmost marker, and restore the two-zero separator. The machine is at R(k+1), with the entire right half-line blank.

The exact cost is 3+k+1+3k+6=10+4k, positive for every k. In particular the kth return is at primitive time 5+10k+2k(k-1)=2k²+8k+5. No E1 or F1 query occurs in any block, or in the initial prefix. Hence every finite step count is reached by every completion, proving nonhalting independent of those slots.

## Formal interface

- Box27GrowingBlock.lean states the exact stream recurrence and its all-time safety consequence.
- Box27GrowingBlockSource.lean projects the original sparse knownRun into that stream model, proves compatible_never for arbitrary completions, and gives parent_never / parent_bound on the actual source Box27.
- These files are proof candidates until the named original-source theorem and axiom audit pass. No local Lean invocation was available in this session.

The existing sibling work on Box28 and Box33 concerns different C0 domains. This cylinder is not counted as a complete parent Cover; the remaining Box27 branches must still be closed. The exact return family provides a reusable external leaf for a later first-hole partition of D0=14,D1=17,E0=21.
