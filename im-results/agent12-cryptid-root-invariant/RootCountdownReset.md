# Root-connected countdown and zero-remainder reset family

**Status (2026-11-22):** Source-branch derivation and reproducible finite replay; not yet compiled as a Lean theorem. Unlike the withdrawn growth macro, every ordinary branch used below has been checked against the pinned #85 source. The path through D65(2) uses no token-normalizer closure. No halting/nonhalting conclusion follows yet.

## Definitions

In first-coordinate notation let

[
D_n(c)=CR([0],0^{4n+5}++[c]).
]

The source-accurate countdown recurrence is

[
D_n(c)\longrightarrow^{8n+24}D_{n+1}(c-3)
\qquad(c\ge3),
]

with raw TM cost (24n+69). Its exact phase decomposition and Lean sweep draft are in [RootCountdownSweep.md](./RootCountdownSweep.md) and [RootCountdownSweep.append.lean](./RootCountdownSweep.append.lean).

The second source-accurate recurrence is the zero-remainder reset:

[
D_n(0)\longrightarrow^{8n+41}D_0(8n+13),
]

with raw TM cost

[
16n+105.
]

Here (D_n(0)) is equivalently (CR([0],0^{4n+6})).

## Zero-remainder reset phase decomposition

The reset is a composition of two zero sweeps and two fixed corridors.

| Phase | Outer successors | Raw TM steps | Endpoint |
|---|---:|---:|---|
| Fixed prefix | 8 | 21 | (EL([0,1],0^{4n+7})) |
| EL zero sweep | (4n+7) | (8n+14) | (EL(0^{4n+8}++[1],[])) |
| EL empty-left | 1 | 1 | (CR(0^{4n+8}++[1],[0])) |
| CR zero sweep | (4n+8) | (8n+16) | (CR([1],[8n+16])) |
| CR one/empty-tail | 1 | 6 | (EL([0],[0,8n+19])) |
| Fixed tail | 16 | 47 | (D_0(8n+13)) |
| **Total** | **(8n+41)** | **(16n+105)** | |

The fixed prefix is the same eight source branches used in the countdown proof, specialized to (c=0). The EL sweep repeats the source EL-right-zero clause (`execute 2`) (4n+7) times. The CR sweep repeats the source CR-left-zero clause (`execute 2`) (4n+8) times. The single CR-left-one / empty-tail branch is the source clause at #85 lines 919–926, with output (EL([0],[0]++bumpPairHead^3(R))).

The 16-step tail starts at (EL([0],[0,8n+19])). Its branch sequence and raw costs are:

1. EL-right-zero (2)
2. EL-positive (1)
3. DL-positive (4)
4. DR-left-zero/right-one (4)
5. DR-left-zero/right-one (4)
6. DR-empty-left (1)
7. EL-positive (1)
8. DL-right-zero (6)
9. EL-right-zero (2)
10. EL-right-zero (2)
11. EL-positive (1)
12. DL-positive (4)
13. DR-left-zero/right-one (4)
14. DR-left-zero/right-one (4)
15. DR-left-zero/right-one (4)
16. DR-positive/positive (3)

It ends at (CR([0],0^5++[8n+13])). The raw cost is 47.

The arithmetic is

[
8+(4n+7)+1+(4n+8)+1+16=8n+41,
]

[
21+2(4n+7)+1+2(4n+8)+6+47=16n+105.
]

A direct source-clause replay checked this reset for every (0\le n\le100); all endpoints, successor counts, and raw costs matched. This finite check is not a proof.

## Root connection

The #490 blank-entry theorem gives the mirror of #85 (DR([0,0],[1])) after 7 raw TM steps. The next 28 ordinary #85 stack successors reach (D_0(3)) at raw time 87. This prefix uses no token closure. Composing the countdown and zero-reset recurrences then gives the following root-connected checkpoints:

| Outer successor index from #85 seed | State | Raw TM time from blank |
|---:|---|---:|
| 0 | (DR([0,0],[1])) | 7 |
| 28 | (D_0(3)) | 87 |
| 52 | (D_1(0)) | 156 |
| 101 | (D_0(21)) | 277 |
| 437 | (D_7(0)) | 1,264 |
| 534 | (D_0(69)) | 1,481 |
| 3,110 | (D_{23}(0)) | 9,140 |
| 3,335 | (D_0(197)) | 9,613 |
| 21,535 | (D_{65}(2)) | 64,018 |

The composition arithmetic is:

- (D_0(3)\to D_1(0)): 24 successors, 69 raw steps.
- (D_1(0)\to D_0(21)): 49 successors, 121 raw steps.
- (D_0(21)\to D_7(0)): 336 successors, 987 raw steps.
- (D_7(0)\to D_0(69)): 97 successors, 217 raw steps.
- (D_0(69)\to D_{23}(0)): 2,576 successors, 7,659 raw steps.
- (D_{23}(0)\to D_0(197)): 225 successors, 473 raw steps.
- (D_0(197)\to D_{65}(2)): 18,200 successors, 54,405 raw steps.

Thus the corrected root path reaches (D_{65}(2)) after 21,535 outer stack successors from the #85 seed and raw TM time 64,018 from blank. This chain uses only the countdown recurrence and the zero-remainder reset; no CR 1,0 / 1,1 / 1,≥2 branch and no token closure is involved.

## What remains open

The next observed transition from (D_{65}(2)) appears to enter a token-normalizer closure and eventually return to (D_0(539)) in the exploratory simulator. That extension is not included in the source-validated chain above: the token-normalizer port and the general remainder-2 reset still need an independent Lean/source audit.

The sequence of zero-remainder reset outputs is suggestive but not itself a nonhalting proof. To establish nonhalting, prove a complete invariant or a parametric return theorem that handles every remainder class reached by iteration. In particular, the subsequent remainder-1 case must be resolved rather than inferred from finite simulation.

The old 1,131,748-step growth seed and 76-step right-insertion macro remain withdrawn; they are not used in this corrected chain.


## Lean proof plan

The source-local append draft is
[`RootCountdownSweep.append.lean`](./RootCountdownSweep.append.lean). It now
contains the one-step CR/EL/DL/DR clauses, the EL-zero and DR-zero sweep
inductions, the CR-one/empty-tail step, and a singleton-right CR-zero sweep
for the reset. The remaining composition is mechanical but not yet checked:

1. Prove the common eight-step prefix from (D_n(c)) to
   (EL([0,1],0^{4n+6}++[c])), specializing (c=0) for the reset.
2. Apply the EL-zero sweep with (4n+7) zeros.
3. Apply EL-empty, then the singleton-right CR-zero sweep with (4n+8)
   zeros and initial right head 0.
4. Apply the CR-one/empty-tail helper to obtain (EL([0],[0,8n+19])).
5. Compose the fixed 16-step tail using the listed source helpers.
6. Normalize the final list arithmetic and compose this reset with the
   countdown recurrence and the finite root prefix.

No local Lean compile or CI result is claimed for this draft.
