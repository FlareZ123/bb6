# Nonhalting of a six-state one-hole machine by a ternary odometer invariant

**Theorem (elementary, self-contained proof).** Let (P) be the six-state two-symbol partial Turing machine with rows, in A0,A1 / B0,B1 / … / F0,F1 order,

```text
1RB 1RA  /  1RC 0RF  /  0RD ---  /
1LD 1LE  /  0RA 0LE  /  0RC 0RB
```

Equivalently, its exact canonical table is
`1RB1RA_1RC0RF_0RD---_1LD1LE_0RA0LE_0RC0RB`.
Every complete machine extending (P) runs forever from the all-zero tape in state A, and never visits the undefined C1 transition.

This is global hard-leaf **6209** in the canonical Raw56 E1=0LE open roster. The argument below is mathematical and does not rely on a time-limited simulation. **This manuscript has not yet been independently kernel-formalized in Lean**; it presents an explicit induction and a finite transition calculation that can be ported into Lean.

## The invariant

Partition cells at nonnegative coordinates into consecutive blocks of seven cells, starting at cell zero. Write

```text
Z = 0000000
U = 0111000
V = 1111111.
```

A *digit configuration* is a tape that is blank at every negative coordinate, is a concatenation of these three blocks at coordinates (0,1,2,ldots), and has only finitely many nonzero blocks (that is, all sufficiently far-right blocks are (Z)). Its head is at coordinate (7j) in state A for some (j\ge0), and **all blocks strictly to the left of (j) are (V)**. The blocks at and to the right of (j) may be any of (Z,U,V), subject to eventual (Z). The initial blank-tape configuration is a digit configuration with (j=0).

The key is a three-case transition lemma for **every** (j\ge0) and every allowed right-hand suffix:

| Current block (j) | Exact number of ordinary TM steps | Resulting blocks and head |
| --- | ---: | --- |
| (Z) | (8+7j) | All (j) preceding (V) blocks become (Z); block (j) becomes (U); head returns to cell 0, state A |
| (U) | (14+7j) | All (j) preceding (V) blocks become (Z); block (j) becomes (V); head returns to cell 0, state A |
| (V) | (7) | Tape unchanged; head advances to cell (7(j+1)), state A |

Every cell to the right of block (j) is unchanged in all three cases. These steps contain no undefined transition. Consequently, every macro successor is again a digit configuration: in the first two cases the head is at the first block (there are no required preceding (V) blocks), and in the last case the preceding (j+1) blocks are all (V).

## Proof of the transition lemma

All head offsets in the following finite traces are relative to the beginning of block (j), i.e., to cell (7j). An entry such as `A0 → B+1` specifies the source state and scanned symbol and the state/relative head offset after one ordinary transition. The writes and directions are exactly those in the displayed table.

**Case (Z).** On the block `0000000`, the six ordinary transitions beginning in A and ending in E are

```text
time  state  relative head  scanned bit
  0     A         0             0
  1     B        +1             0
  2     C        +2             0
  3     D        +3             0
  4     D        +2             0
  5     D        +1             1
  6     E         0             1
```

The current block is now `1111000`, and the (j) preceding blocks are still (V). From this position E reads a **contiguous run of precisely (7j+1) ones** (the first cell of the current block followed by all the preceding (V) blocks). Each E1 rule writes zero and moves one cell left, leaving E on coordinate (-1). At coordinate (-1) the tape is zero, so one E0 rule moves right into state A at cell 0, without writing a one. The current block is then exactly (U=0111000); preceding blocks are all (Z). Number of steps: (6+(7j+1)+1=8+7j). The trace never reads a cell beyond block (j).

**Case (U).** On `0111000`, the first thirteen transitions are

```text
time  state  relative head  scanned bit
  0     A         0             0
  1     B        +1             1
  2     F        +2             1
  3     B        +3             1
  4     F        +4             0
  5     C        +5             0
  6     D        +6             0
  7     D        +5             0
  8     D        +4             0
  9     D        +3             0
 10     D        +2             0
 11     D        +1             0
 12     D         0             1
 13     E        -1             1 if j>0, else 0
```

At time 13 the current block is (V=1111111), and E is immediately to its left. If (j>0), the preceding (7j) cells are all one, so exactly (7j) E1 transitions erase them and move E to coordinate (-1); if (j=0), E is already at (-1). In either case, one E0 transition returns to A at cell 0. The resulting current block is (V) and all preceding blocks are (Z). Number of steps: (13+7j+1=14+7j). The only visit to state C is on the zero at relative offset +5; no transition beyond the current block is inspected.

**Case (V).** On `1111111`, seven A1 transitions write ones without change and move the head right by seven cells, leaving it in state A at the next block boundary. Nothing else is read or written.

Thus all three identities hold uniformly for every (j\ge0) and arbitrary allowed right suffix, completing the transition lemma.

## Infinite-time conclusion

Starting from the blank tape, apply the transition lemma repeatedly. Every successive configuration is a digit configuration and every macro takes at least seven ordinary steps, all defined within the partial table. By induction, for each (n\in\mathbb N) the machine executes at least (7n) nonhalting ordinary steps from the blank tape. Therefore it does not halt at any finite time. The proof used no C1 transition, hence it applies to **every** assignment of that remaining slot, including halting assignments. (□)

## Source identity and implications

The exact partial table above is leaf 6209 of the pinned Raw56 E1=0LE canonical source cut (26,493 open leaves, SHA256 `aba63f28439c707c3343fd4ff53f66717d5924b88b1aa8012947f6039e0da7ef`). It was among the 18 previously experiment-hard leaves of E0=0RA. A straightforward finite simulation over (j=0,dots,50), all three current digits and each of three possible next-block values (459 tests) independently agrees with all three macro claims; **simulation is corroborative, not part of the proof**.

The invariant is a genuine symbolic three-valued odometer over an unbounded sequence of seven-bit cells, rather than a fixed-state or fixed-window abstraction. It resolves one **additional explicit nonhalting partial-machine cylinder** (leaf 6209). It does **not** prove nonhalting for all other E0=0RA leaves, nor determine BB(6). To integrate with the repository's source-audited universal parent classifier, formalize the three parametric trace identities as original Lean source theorems and consume `never` at the canonical leaf.
