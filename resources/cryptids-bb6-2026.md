# Independent formalization of the six-state #746 machine

## Sources

- Research paper: “At the Limits of Computability: Steps Towards Autonomous AI Discovery on the Busy Beaver Frontier”, arXiv:2610.22603 (15 October 2026): https://arxiv.org/abs/2610.22603
- Public Lean repository: https://github.com/google-deepmind/cryptids
- Exact machine module: https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean
- Hardness summary: https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/Hardness.lean
- General challenge definitions: https://github.com/google-deepmind/cryptids/blob/main/BusyBeaverChallenge.lean

The machine RLE in the paper and module is the same six-state machine studied in this repository:
1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA.

## High-level C(a,b) map

The machine-specific module proves a high-level acceleration with start state C(0,2). Its first transition reaches C(2,0), the source reset root used by the FlareZ123/bb6 development. The high-level transition map is:

1. C(a,0) maps to C(2,2a+1).
2. C(a,1) halts.
3. For b>=2, let d=b-2.
   - If d>=2a, map to C(2a+2,d-2a).
   - If d<2a and d is odd, map to C(floor((6a+d+5)/4),(6a+d+5) mod 4).
   - If d<2a and d is even, map to C(floor((6a+d+8)/4),(6a+d+8) mod 4).

This is an exact formalized accelerated map in the external repository. It does not itself prove that the blank-derived orbit halts or never halts.

## Drain calculation

Starting from C(a,0), the first step is C(2,2a+1). During the high-b drain branch, after m valid drain transitions the state coordinates have the closed forms

- A_m = 2^(m+2)-2;
- B_m + 8*2^m = 2a+9+2m.

The halting state is C(A_m,1). Substituting B_m=1 gives

a = 4*2^m-m-4.

This is exactly the fatal-height formula used in FlareZ123/bb6. The drain conditions must hold for every preceding transition; for a equal to the displayed target, the preceding drain inequalities hold and the target is reached.

## The 3/2 underflow and the odd ResetParent equation

When the low modulo-four branch reaches C(y,2), define c=y+3. If y is odd, then the next high-level transition sends

c -> 3c/2,

and the second coordinate remains 2 precisely while the new c is even. Write c=2^t z with z odd. After t such underflow transitions, c=3^t z is odd; the final C(y,2) transition returns to a state C(g,0) satisfying

2g+5 = 3^(t+1) z.

The local source odd-parent equation also requires

2^(t+1) z = 8*2^l+x+l+5.

These equations match the odd ResetParent constructor in the FlareZ123/bb6 source grammar and the GapOddParent(g) witness added in TThreeHighTTwoOne.lean. This is an algebraic alignment. A formal theorem refining the external C(a,b) transitions to the local ResetParent relation has not yet been added.

## Reported hardness evidence

The external Hardness.lean note describes a partial exact even-c underflow invariant, 1,253 cascades, and an estimated hazard around 10^-294. The hazard is a heuristic estimate. It is not a proof of non-halting and does not resolve the machine.

## Research opportunity

Build a formal bridge between the external high-level map and the local source ResetParent grammar. Then express the blank-derived C(2,0) orbit as an exact deterministic one-dimensional return map and investigate whether its iterates can ever hit the fatal-height set. This may unify the source-root inverse analysis with the independent Collatz-like acceleration.


## Local Lean verification of the odd underflow tail

FlareZ123/bb6 now contains HighLevel746Underflow.lean, a Lean transcription of the C(a,b) high-level map and proofs of its exact b=2 underflow. The shifted coordinate c=a+3 follows c -> 3c/2 while even. For c=2^t z with z odd, t such transitions reach 3^t z, and the final transition reaches C(g,0) with 2g+5=3^(t+1)z.

TThreeHighTTwoOneHighLevel.lean proves that a local GapOddParent(g) witness yields this finite underflow path from C(2^t z-3,2) to C(g,0), retaining the source predecessor x and the scale equation. The preceding high-b drain from C(x,0) to the intermediate C-state remains open. The new modules have been checked locally; targeted full-source CI is pending.
