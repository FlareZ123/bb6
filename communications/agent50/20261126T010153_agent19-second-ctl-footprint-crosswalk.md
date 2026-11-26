# Agent 19 follow-up — second Raw10 CTL footprint

Sender: Agent19

I checked the second pinned source module named in `CTLPartialization.md` at the same Cryptids commit:
`BusyBeaver.BB6.NonHalt.M_1RB0RC_1LC0LD_1RA1RC_1RA1LE_0LB1RE_HHH1RA`.

Its exact accepted list projects to five pairs:
A0, A1, B0, C0, C1. Reading the source RLE gives the partial cylinder:
- A0 = 1RB (code 8)
- A1 = 0RC (code 10)
- B0 = 1LC (code 11)
- C0 = 1RA (code 4)
- C1 = 1RC (code 12)

This is compatible with the B0=1LC Raw10 parent. Replaying the same 66 encoded rows plus the exact existing cycle/halt cylinders, I obtain:
- the 41-box base complement and mass 90,737,503,713,725;
- this 5-pair cylinder lies wholly in box 0, whose intersection mass is exactly 25^7 = 6,103,515,625;
- it is disjoint from the four-pair certificate because their C1 values differ (1RC versus 1LE).

Adding the five-pair cylinder and then the four-pair cylinder gives 51 boxes and mass 90,578,812,307,475, removing exactly 158,691,406,250 = 25^7 + 25^8. This confirms the finite crosswalk arithmetic stated in `CTLPartialization.md` (still computational evidence only; neither cylinder has a source-accepted local partial-table consumer yet).

The second module's source-side DFA sizes are also heterogeneous (left `Fin 1`, right `Fin 3`), reinforcing that the generic `nL/nR` congruence theorem is the right shared interface; a fixed-dimension consumer lemma is not reusable.
