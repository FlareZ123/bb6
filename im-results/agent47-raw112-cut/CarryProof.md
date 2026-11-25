# Raw112 F1 siblings: recursive carry and exact simulation

**Status: both one-hole residuals are source-certified nonhalting.** Lean 4.36.0-rc2 original-source CI [45595822219](https://github.com/FlareZ123/bb6/actions/runs/45595822219) compiled both adapters with only standard axioms. The full parent weighted cover remains pending.

Exact tables: `1RB0RF_1RC0LB_0RD0LB_1LD1RE_0RA1LC_---0LE` and `1RB0RF_1RC0LB_0RD0LB_1LD1RE_0RA1LC_---1RB`. Both have only F0 unassigned; every compatible completion is nonhalting.

## F1=0LE

The blank run reaches C after 382 primitive steps, with scanned 0, nearest-first left word 1, and right word 00 (110000)^n 001111 L(n mod 6) H(floor(n/3)), n=1. The invariant holds for every n >= 1, using the base-six encoding observed by Agent19.

- Raw112CarrySweeps: arbitrary-context local sweeps, pumped by induction. Three outer sweep sections cost 88j+165, 50j+85, 12j+26, with j=n-1.
- Raw112HighIncrement: H(k) has six seeds; for k=6m+r, m>=1, a parity-dependent 15-bit digit prefix is followed by H(m). The E increment is proved by strong induction, returning D on even k and B on odd k. Ordinary digit transitions preserve arbitrary contexts. Carry r=5 recurses on m; even m costs 77+t+23 and odd m costs 75+t+15. Base carry k=5 costs 121.
- Raw112CarryRoot: six low phases compose both suffix operations with the outer sweep theorem, proving positive-cost growth from family j to family (j+1). Entry and unbounded_live prove arbitrarily long successful primitive prefixes.
- Raw112CarryNever: source-certified NeverHalts adapter.

## F1=1RB

Raw112Sibling proves an exact four-to-two-step correspondence from A/1 with right neighbor 1: the long path goes A/1, F/1, E/0, A/0; the short path goes A/1, F/1, reaching identical B configurations. A/1 followed by blank fails in two steps, contradicting any four-step live original prefix. All other non-F configurations take the same step without entering F. Induction on N transfers original live prefixes of length at least 4N to sibling prefixes of length at least N. Raw112SiblingNever is the source-certified NeverHalts adapter.

## Parent closure

Raw112ClosedCover attaches both certificates to the actual generated residual tables via a finite twelve-entry table comparison. It proposes WeightedBound 100000 for the parent `1RB---_1RC---_0RD---_1LD1RE_---1LC_------`. Full parent audit still pending. No global BB(6) bound is established.

Initial source attempts failed from a transcription error (R for L in the right-sweep proof). Commit 517ebe6f7f1c8e75d22e4ff6dee7ea2518100ecb restored the exact local blob ed471205ea84caffa44ca0a9d93634ae949201fc. The corrected CI succeeded.
