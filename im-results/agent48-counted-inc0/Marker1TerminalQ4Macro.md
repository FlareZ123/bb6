# Marker-1 even-L q4 macro: checkpoint structure and exact z=0 arithmetic

**Status:** intermediate computational/Lean result. This is not a proof that the complete TM6 candidate halts, and it is not an upper bound for BB(6).

## Scope and source configuration

Use the standard two-symbol TM2 transition table. The S0 input family is

```lean
s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) A z 0 h
```

with `A >= 1`, even `L >= 2`, and `0 <= z < 2^A`. Its left-facing tape begins with `binDec A z`; the right-facing tape is `s0RightFacing 0`.

Put

\[
M=2^A(2^{L+2}-1),\qquad w=A+L+2.
\]

A distinguished checkpoint is a configuration in state 4, reading 0, with head at coordinate 1. Number these checkpoints `j=1,2,...`.

## General left checkpoint frame (experimental)

For `z=0,1,2,3`, the checkpoints tested satisfy the same exact finite-support left-facing word:

\[
\boxed{\quad 011\;\Vert\;\operatorname{binDec}(w,M-j)\;\Vert\;lh.\quad}
\]

The right-facing word is not yet reduced to a comparably simple formula for general `z`; it carries a nested counter and its observed size/shape changes substantially as `z` grows. Do not extrapolate the `z=0` right frame to positive `z`.

The independent checkers `marker1_terminal_q4_checkpoint.py` and `marker1_terminal_q4_block_sim.cpp` verify the entire left half of the finite-support tape at each sampled checkpoint, not just a bounded prefix. The Python checker records a right-window run-length encoding without asserting a general right-frame formula. The C++ checker uses sparse 64-cell blocks and supports multi-billion-step runs.

Checked checkpoint prefixes:

| `A` | `L` | `z` | `M` | checkpoints checked | checkpoint steps |
|---:|---:|---:|---:|---:|---|
| 1 | 2 | 0 | 30 | 3 | 143, 229, 359 |
| 4 | 2 | 1 | 240 | 3 | 287, 445, 647 |
| 3 | 2 | 2 | 120 | 3 | 503, 1285, 105095 |
| 3 | 2 | 3 | 120 | 2 | 1031, 104785 |

The corresponding q4/read-0 event indices at those checkpoints are respectively `8,13,18`; `14,22,30`; `23,49,435`; and `38,424`. For `A=4,L=2,z=1`, the left frame was checked at all 240 checkpoints; the machine halts at step 953,013 with 1,930 q4/read-0 events.

These are finite computational observations, not a formal transition proof.

## Fully checked special case `z=0`

For `z=0`, the right-facing checkpoint word also has a simple exact form:

\[
000\;\Vert\;1^{5j}\;\Vert\;00111.
\]

There are exactly `M` checkpoints and `7+5M` state-4/read-0 events. The five event-head coordinates in ordinary cycle `j` (`1 <= j < M`) are

\[
1,\quad -(3r+2),\quad 5(j+1),\quad 5(j+1)+3,\quad 5(j+1)+7,
\qquad r=v_2(M-j).
\]

The exact measured/verified time decomposition is:

- Initial prefix to checkpoint 1:
  \[
  P=107+12(A+L).
  \]
- Ordinary cycle `j` to `j+1`:
  \[
  C_j=20(j+1)+46+12v_2(M-j).
  \]
- Final cycle from checkpoint `M` to halt:
  \[
  C_{\rm final}=5M+12(A+L)+76.
  \]

The terminal five event-head coordinates are

\[
1,\quad -(3(A+L+4)+2),\quad -(3(A+L+3)+1),\quad 2,\quad 5M+6.
\]

`marker1_terminal_q4_macro.py` independently simulates the full finite-support tape and checks every checkpoint tape, every ordinary five-event head pattern, every ordinary cycle cost, the terminal head pattern, the prefix, the terminal cost, and the final halting step.

Its six checked cases are:

| `A` | `L` | `M` | total steps |
|---:|---:|---:|---:|
| 1 | 2 | 30 | 11,319 |
| 2 | 2 | 60 | 40,521 |
| 3 | 2 | 120 | 152,913 |
| 1 | 4 | 126 | 168,111 |
| 2 | 4 | 252 | 653,601 |
| 1 | 6 | 510 | 2,638,407 |

## Lean-verified arithmetic for the `z=0` macro

`Marker1TerminalArithmetic.lean` compiles with Lean 4.36.0-rc2 and proves, from the elementary recurrences for `v2` and binary popcount,

\[
\sum_{r=1}^{M-1}v_2(r)=M-A-L-2.
\]

It also proves the linear cycle sum

\[
\sum_{j=1}^{M-1}(20(j+1)+46)=10M^2+56M-66,
\]

and formally derives the total `z=0` macro arithmetic:

\[
\boxed{T=10M^2+73M+93+12(A+L).}
\]

With `N=5M+7`, Lean also verifies the equivalent expression

\[
T=\frac{2N^2+45N+60(A+L)+52}{5}.
\]

Important scope restriction: the Lean file proves the valuation sum and the algebraic collapse **conditional on the displayed cycle-cost decomposition**. It does not prove the TM2 prefix, checkpoint, cycle, or terminal-run lemmas. The simulator is independent computational evidence for those claims, not a substitute for their formal proof.

## Positive-z nested-cycle observations (conjectural)

For z >= 1, the q4 event counts between successive checkpoints grow rapidly. The observed counts are:

| z | j | q4/read-0 events between checkpoints |
|---:|---:|---:|
| 1 | 1 | 8 |
| 1 | 2 | 8 |
| 2 | 1 | 26 |
| 2 | 2 | 386 |
| 3 | 1 | 386 |
| 4 | 1 | 98,306 |

A revised conjecture fitting these data is

\[
K_j(z)=(2^{z-1}-1)(2^{2^{j-1}}-1),\qquad
E_j(z)=6\cdot4^{K_j(z)}+2.
\]

The earlier candidate with factor (2^j-1) is falsified: for A=3,L=2,z=2, a 7-billion-step run accumulates 102,460 q4/read-0 events after checkpoint j=3 without reaching checkpoint j=4, whereas that earlier candidate predicted only 98,306. The revised factor (2^{2^{j-1}}-1) predicts 6,442,450,946 events for that cycle and is consistent with the run, but remains a conjecture.

### First-cycle cost law (strong computational evidence)

Let k=2^z-1. Across z=1,2,3,4 and several independent A,L choices, the first q4-checkpoint cycle cost is independent of A and L in every tested case and matches

\[
\boxed{C_1(z)=\operatorname{drainCost}(2^z-1)+12(2^z+z+6)+2}
\]

or, after simplifying the repository's counted-drain formula
\[
\operatorname{drainCost}(k)=6\cdot4^k+42\cdot2^k-12k-48,
\]
\[
C_1(z)=6\cdot4^{2^z-1}+42\cdot2^{2^z-1}+12z+38.
\]

The first-cycle q4/read-0 event count matches
\[
E_1(z)=6\cdot4^{2^{z-1}-1}+2.
\]

Checked data:

| z | (A,L) cases | first-cycle steps | q4 events |
|---:|---|---:|---:|
| 1 | (3,2), (4,2) | 158 | 8 |
| 2 | (3,2), (4,2), (2,4) | 782 | 26 |
| 3 | (3,2), (4,2), (3,4) | 103,754 | 386 |
| 4 | (3,2), (4,2), (3,4) | 6,443,827,286 | 98,306 |

For z=3,(A,L)=(3,4), checkpoints 1 and 2 occur at steps 1,055 and 104,809. For z=4, the second checkpoint occurs at 6,443,829,913 for (3,2), 6,443,829,925 for (4,2), and 6,443,829,937 for (3,4); all three first-cycle costs are identical. The left checkpoint frame is checked at both endpoints.

For j=1, 2K_1(z)+1=2^z-1, so the first-cycle law is exactly the existing counted-drain cost at width 2K_1+1 plus the displayed 12(2^z+z+6)+2 frame overhead. This strongly suggests a counted-drain subrun, but no source-level decomposition has yet been proved.

For later cycles, the conjectured width remains 2K_j(z)+1. For example, z=2,j=2 has K=3, drainCost(7)=103,548, and observed cycle cost 103,810 (overhead 262); z=3,j=1 has the same drain width and observed cost 103,754 (overhead 206). The later-cycle overhead formula and the exact prefix/postlude decomposition remain open.

The sparse 64-cell-block C++ simulator marker1_terminal_q4_block_sim.cpp verifies the complete left checkpoint frame and supports multi-billion-step runs. It does not prove halting or establish a general positive-z right-side macro.

## Critical root-connection caveat

The `z=0` terminal law is not, by itself, a closure of the current `m=2,n=1` root path. The root endpoint is

```lean
s1Config L 0 1 (a+b+2) (2^b-1) 0 h'
```

and the repository proves the relevant first-section right counter is at least 2. Thus the endpoint has a positive, in fact at least 3, binary counter `z=2^b-1`. The `z=0` macro above does not directly apply.

The existing `S1CountedDrain` theorem can move an all-ones binary counter into the right unary counter, but that produces a nonzero right counter; the `z=0,b=0` terminal macro still cannot simply be invoked. The next substantive task is to formalize the positive-z nested q4 macro (or find a different composition that reaches the `z=0,b=0` family).

## Next proof targets

1. Formalize the general left checkpoint frame in Lean for arbitrary `z`.
2. Identify the right-side checkpoint state as an explicit nested counter, rather than a bounded tape sample.
3. Prove or refute the event-count conjecture `E_j(z)` adversarially.
4. Identify the exact counted-drain subrun and derive the prefix/postlude costs from existing `drainCost` and reset-prefix lemmas.
5. Prove the terminal `j=M` run and connect the positive-z macro to the authentic root endpoint.

Until these obligations are discharged, all positive-z cycle formulas remain experimental and no BB(6) value is claimed.
