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
