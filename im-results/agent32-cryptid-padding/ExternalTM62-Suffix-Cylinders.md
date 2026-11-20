# Suffix-extended halting cylinders from the external 108-step proof

**Status:** exploratory exact finite-tail simulation plus a parametric proof reduction. The additional suffix cases below are not yet Lean-kernel checked. Keep this in `im-results/`; do not promote to `results/` or describe them as accepted theorems.

## Reduction

The pinned external theorem proves that
`A(3^108*k + C, [])` halts, where
`C = 1975700577069254261393123959451562008800234946348086`.

The 107 `A_step2` calls are built from `step_An_1101` lemmas with an arbitrary suffix parameter. Their endpoint for the empty suffix is
`A(3*8^107*k + C2, P)`, with
`P = [0,1,0,1,1,0,1,1]`.
The suffix-preserving composition can be replayed with an arbitrary initial suffix `r`; the corresponding endpoint should be
`A(3*8^107*k + C2, P ++ r)`.
This parametric endpoint statement must be made explicit and kernel-checked before accepting the generalization.

Since `C2 mod 3 = 1`, the final `step_An_1101` takes its E branch. Its endpoint has:
- state E;
- scanned symbol `P.head = 0`;
- left stack `[0,0] ++ [1,0]^(4*(n/3)-1) ++ [1,1] ++ 0^∞`;
- right stack `P.tail ++ r ++ 0^∞`.

For the huge unary parameter in this cylinder, the alternating left block is longer than any of the finite traces below. The final tail is therefore a small deterministic computation depending only on the canonical suffix `r=(01)^q 1^b`.

## Positive tail computations

I replayed the exact six-state D0 table from the final E configuration, with the left stack above and the right stack `P.tail ++ (01)^q ++ 1^b ++ 0^∞`. The empty-suffix case reproduces the external proof's 113-step tail exactly, which is a useful calibration of the local tape orientation.

| Canonical suffix r | q,b | Final raw steps to F/1 | Max head displacement right | Min head displacement left |
|---|---:|---:|---:|---:|
| empty | (0,0) | 113 | 10 | -5 |
| 01 | (1,0) | 127 | 13 | -5 |
| 011 | (1,1) | 74 | 12 | -2 |
| 0101011 | (3,1) | 131 | 16 | -5 |
| 010101011 | (4,1) | 153 | 18 | -5 |

Thus, **conditional on the parametric 107-call endpoint**, these four additional candidate families follow by finite raw computation:
[
 A(3^{108}k+C,(01)^q1^b) 	ext{halts}
]
for ((q,b)=(1,0),(1,1),(3,1),(4,1)).

The positive trace computations are exact finite simulations of the explicit transition table, not yet Lean proofs. The trace lengths above are the first time F/1 is reached. The finite left-window bounds are at most five cells; the right-window bounds are shown in the table. The terminal tails use the default blank after the stated finite suffix.

A small search over (0\le q\le20), (0\le b\le30), with a 2,000-step horizon found no further halting cases in that rectangle. This is only a bounded search; it is not a theorem that other suffixes do not halt.

## Why this matters to the D-root program

The suffixes ((01)^q1^b) are exactly the canonical DRegular suffixes used by `L(a,q,b)`. The external halting cylinder therefore need not be restricted to the pure-unary section `q=b=0`: it also supplies candidate halting classes at `q,b=(1,0),(1,1),(3,1),(4,1)`, all at the same unary residue (a\equiv C\pmod {3^{108}}).

The D-root exception table in `im-results/agent2-root-language-exit/seed31-38-exact-replay.md` has:
- (8,1), residue 39637;
- (1,1), residue 58126;
- (5,1), residue 49579;
- (6,1), residue 55039;
- (9,1), residue 54265;
- (7,1), residue 27469;
- (6,1), residue 50584;
- (1,1), residue 24670.

But (C\bmod 59049=23839). None of these eight exceptional states is in any of the candidate cylinders, already at the weaker modulus (3^{10}=59049). In particular, the two known q=1,b=1 root exceptions are not hits of this specific C-cylinder. This is an exact low-modulus exclusion for those listed exception states, not an all-time exclusion of the root orbit.

The new cases (1,0), (3,1), and (4,1) are worth checking against regular intermediate states and later root episodes, not just the exception endpoints. A root state in one of these suffix classes with (a\equiv23839\pmod{59049}) would be a necessary first filter for the full (3^{108}) congruence.

## Reproducible tail simulator

The local simulation uses the D0 table:
`A0→1RB, A1→0RE, B0→1LC, B1→0RA, C0→1LA, C1→1LD,
D0→1LC, D1→1LF, E0→0LC, E1→0LB, F0→1LE, F1→halt`.
It initializes state E, head symbol 0, left stack `[0,0] ++ (1,0)^m ++ [1,1]`, and right stack `[1,0,1,1,0,1,1] ++ (01)^q ++ 1^b`. It advances the deterministic table until F/1 or the stated horizon, recording head displacement. This is the exact same table as `BB6.Portfolio.D0`; the external TM62 table has the same eleven live entries after A–F↦0–5 and S0/S1↦false/true.

## Kernel-acceptance path

1. State the suffix-parametric 107-call endpoint `A(...,P ++ r)` explicitly, using the existing `A_step2` composition rather than assuming it from the empty-suffix theorem.
2. For each of the four suffixes, unfold the final `step_An_1101` E branch and use `iterate 127 stepHalt`, `iterate 74 stepHalt`, `iterate 131 stepHalt`, or `iterate 153 stepHalt` respectively.
3. Audit the transitive axiom profile and verify that the exact source transition table is used.
4. Only then treat the four extended cylinders as formal results.

This does not prove that the authentic blank-root orbit reaches any of these cylinders. It enlarges the finite set of certified targets that the root-reachability investigation can search for.
