# Raw47 hard leaf 3312: ternary carry invariant

The table `1RB---_1RC1RF_0RD0LE_1LD0RC_1LB1RA_0RA0LF` is row 3312 in Agent12's `agent12-raw47-rungraph/hard10.txt`. All completions of its A1 hole are nonhalting, by a positive-cost return invariant at state A. This is a local kernel proof against the original accepted dependency objects, not yet a complete Raw47 parent audit.

Write the left zipper (including scanned cell) as 0 (11111)^k 0. The right word is a finite sequence of five-bit digits D0=00000, D1=00100, D2=00111, with terminal suffix empty or 001. From blank, 12 steps reach k=0, terminal 001. The exact transition macros are:
- D0 S: after 12+5k moves return at k=0 with D0^k D1 S.
- D1 S: after 16+5k moves return at k=0 with D0^k D2 S.
- D2 S: after 13 moves return at k+1 with S.
- Empty: after 12+5k moves return at k=0 with D0^k 001.
- Terminal 001: after 16+5k moves return at k=0 with D0^k D2.

The F1 left sweep supplies the parametric term 5k; each fixed prefix is an exact definitional reduction for arbitrary suffixes. The invariant is preserved for every k and every grammar word. Induction gives arbitrarily long live prefixes. The original `SweepPumping.run_project`, `Agent50Zipper.zrun_sound` and `run_append` transport the result to `NeverHalts` for all compatible original machines.

`Raw47Ternary3312.lean` compiled locally with Lean 4.36.0-rc2 using the accepted Raw69 artifact 15007309346, SHA256 59ed35c0a1477fd402efc26c36a04d5bbf73d33558a9e2985525c836ce405023, extracted directly to LEAN_PATH. Both `goodStep` and `never` depend only on [propext, Quot.sound]. Reproduce with `LEAN_PATH=/path/to/raw69-artifact lean Raw47Ternary3312.lean`. Use theorem `BB6.Agent2Raw47Ternary3312.never` in the exact open-leaf certificate bank. No global roster reduction is claimed.

## Four further hard leaves

All four new proofs locally compiled against the same accepted Raw69 objects; each `goodStep` and `never` profile is exactly [propext, Quot.sound].

| ID | Digit language (least significant block first) | Terminal representations | Entry | Theorem |
|---|---|---|---:|---|
| 23138 | 00000,01100 | empty,011 | 12 | BB6.Agent2Raw47Binary23138.never |
| 3932 | 00000,10100,01100,00010,10110,01110 | empty,101,011,0001,1011,0111 | 10 | BB6.Agent2Raw47Senary3932.never |
| 27039 | 00000,01000,00010,01010 | empty,010,0001,0101 | 23 | BB6.Agent2Raw47QuaternaryPair.never true |
| 27050 | same | same | 23 | BB6.Agent2Raw47QuaternaryPair.never false |

Binary and senary left stack is 0(11111)^k0; pair left stack is 0111(11111)^k00. A nonmaximum digit increments, writes k zero blocks on the right, and resets k=0. A maximum digit consumes itself and increments k. Binary costs 12+5k,7; senary costs 10+5k,6+5k,12+5k,10+5k,6+5k,7; quaternary costs 38+5k,34+5k,38+5k,5. The binary and senary machines use F1 sweeps; the quaternary pair uses E1 and a fixed 25-step return, valid for both assignments of the three differing rows. Exact arbitrary-tail computations and induction prove all-time original-machine nonhalting, including all completions of the respective hole.

These solve five of the ten historical `hard10.txt` leaves in local kernel proofs. The remaining five are 3423,5258,9918,9919,9920. No claim that the whole Raw47 parent is covered.
