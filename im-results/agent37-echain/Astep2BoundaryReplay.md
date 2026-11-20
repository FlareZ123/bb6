# A_step2 boundary replay and regular-language exit

## Status

A deterministic, dependency-free Node replay of the 107 `A_step2` tails from the pinned external Lean proof now reproduces all eleven published checkpoints, including every unary parameter and suffix. Every tail ends in state C on symbol 1; every boundary marker is even; the alternating block precondition is checked across every cell that the finite tail can disturb.

This is a computational cross-check of the external Lean proof, not an independent formal proof and not a solution of the authentic blank-tape reachability problem.

Reproduce with:

```sh
node Astep2BoundaryReplay.mjs
node Astep2BoundaryReplay.mjs --trace
```

Source proof: [int-y1/proofs, commit 1929f57df4dd7afcc11c3f458e20526fd1f991e0](https://github.com/int-y1/proofs/blob/1929f57df4dd7afcc11c3f458e20526fd1f991e0/BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.lean).

## Exact boundary recurrence

Let the current unary parameter be (N=3q+a), (a\in\{0,1,2\}). The `step_An_1101` endpoint has branch A/E/B according to (a=0/1/2), and alternating-block length

[
m=\begin{cases}
4q-1,&a=0,1,\\
4q+3,&a=2.
\end{cases}
]

The near-to-far left tape is (0^e(10)^m11,0^\infty), where (e=1,2,0) for (a=0,1,2), respectively. Let (n) be the ordinary tail-step count from the external proof. Track the signed displacement (d=\#R-\#L) during these (n) steps. The distance marker from the current head to the base (11) is initially (e+2m+1), and changes by +1 on R and -1 on L. At the end,

[
M=e+2m+1+d=2m'
]

is even, and the inclusive left side begins with ((10)^{m'}). The replay checks the entire region the finite tail can modify, plus a boundary margin; the untouched remainder is the original alternating block.

Let (z) be the number of leading ones in the right tape **after the current head cell**. The external `step_01C_C11` lemma moves ((10)^{m'}) to the right as ((11)^{m'}), and the final two primitive steps traverse the base (11). Therefore the next A-section is

[
N'=2+M+z,\
r'=\operatorname{drop}_{z}(\text{right side after current head}),
]

where the first zero is retained in (r'), and trailing blank zeros are quotiented away by `ListBlank`.

The head-cell distinction matters. Counting the current head as part of (z) creates an off-by-one error in the next residue modulo 3.

## Checkpoint replay

| Completed calls | Unary parameter (N) | Canonical suffix |
|---:|---:|---|
| 10 | `35925965576050291197954676646168812866911688985763244505` | `010101011` |
| 20 | `653274599173389056319717515476765122857837155218448003942322` | `01011101010111` |
| 30 | `11879087870908968104360314522392758770461111276045783640742261386` | `0111010111` |
| 40 | `216008289352335720339610602524813115320952275950623503089297980541682` | `010110111` |
| 50 | `3927875740627220359664132971002588353805172690412603331883223229967369354` | `01111111101` |
| 60 | `71424147101329785314496471805836819044114607618056461822634921267834080686730` | `011011111111` |
| 70 | `1298770410781319861625359536628288369435308900216028055554241136144906066587587722` | `011111101011111` |
| 80 | `23616726952692910182205306669292505610517611280824263889413609179834777358573759023858` | `01011111011111` |
| 90 | `429444486360386240087203819295254784395458238425633310167425409595064063059982219052239602` | `0100101011` |
| 100 | `7808980780222260203826248505306665087325883016528076661998155848237077485933315200811517542561` | `0101011111111011` |
| 107 | `7488166283129708930486796847462680979065226437987146331898837006603604720521272903526417758309106` | `01011011` |

At call 50 the external Lean list retains one final false; the canonical suffix above removes that trailing blank. The two tapes are identical under `ListBlank`.

## Connection to the DRegular section and its first exit

The first ten suffixes are all of the regular form ((01)^q1^b). Their parameters after calls 1–10 are

[
(1,5),(3,2),(2,2),(1,2),(2,0),(1,0),(1,7),(3,4),(2,4),(4,1).
]

The tenth output is therefore the E-branch ((q,b)=(4,1)) boundary. This is exactly the exceptional E, (b=1) case where `DRegularFirstExit` has no regular successor.

The external A-macro continues: call 11 uses branch E and (n=35), producing suffix

[
0111111110111111 = 0,1^8,0,1^6.
]

Thus the suffix has the packet shape `word q=0 p=8 fixedTail`, with `fixedTail = 0 1^6`. It is no longer in the regular ((01)^q1^b) language. This identifies a concrete source-level boundary that the next investigation should align with the existing E-one / exceptional-packet source theorems. Do not identify it with a particular packet theorem solely from the suffix shape; the unary parameter and full source configuration must also match.

## What this establishes—and what it does not

Established computationally:
- the exact 107-call branch word and all 107 tail/block preconditions;
- all eleven unary/suffix checkpoints from the external Lean proof;
- the exact first regular-language exit at ((q,b)=(4,1));
- a compact recurrence that updates unary parameter and arbitrary suffix together.

Not established:
- a Lean theorem formalizing this simulator;
- a general theorem identifying every external A-macro return with `DRegular.next`;
- a bridge from the authentic blank-tape orbit to the external halting cylinder;
- the exact value of BB(6).

The next high-value task is to formalize the marker recurrence in Lean and align call 11's packet-shaped endpoint with the existing exceptional E source closures.
