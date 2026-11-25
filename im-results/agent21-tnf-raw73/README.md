# Raw73: complete candidate closure (2026-11-25)

Parent `1RB---_1RC0LD_0RD---_1LD1RE_---0LB_------`, raw residual 73, B1=0LD, five holes. Deterministic Agent2 enumeration (1000-step cap; 256-step side-cycle lag) yields 599 splits including root, 11,624 cycle leaves, 1,929 last-hole leaves and 225 open leaves; candidate observed weighted maximum 367. The represented raw mass is exactly 25^5=9,765,625 (open mass 32,625). The cap does not certify any nonhalting machine.

224 open leaves have candidate FAR automata. 222 accepted the existing candidate bank (Agent10 specs and Agent31 four-hole data); two further witnesses were found using the seeded FAR mutation search:
- open index 56: `1RB---_1RC0LD_0RD1RF_1LD1RE_0RF0LB_1LA0RC`, orientation+base36 DFA `001213456443434`;
- index 93: `1RB0RF_1RC0LD_0RD---_1LD1RE_1LF0LB_1RA0LE`, DFA `0012345647728747763`.

Both new DFAs pass the exact Python masks recurrence, including the blank-start loop. The last leaf (89, `1RB1LF_1RC0LD_0RD1RC_1LD1RE_1LF0LB_---0LA`) has a one-block sweep candidate, entry 11 and return cost 23+12n, state A, left empty, right 01(0101)^n01.

The committed bank/index and `prepare.py` reproduce the whole candidate audit with the shared generators and split checker; the open-list SHA256 is 55ba96537acce2e6b0bd2fea4ac9bb6768f7ced7cc30db3756f2857e4a5a54c9. `Raw73Bound.lean` exposes a literal-parent weighted bound of 7014 if the original source checks pass. `Raw73CanonicalCut.lean` is a draft independent quotient graft to ingest through the shared core. No new certified cylinder or roster count is claimed until Lean accepts the corresponding theorem.
