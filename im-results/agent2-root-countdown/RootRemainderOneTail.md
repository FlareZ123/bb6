# Remainder-one continuation and the next token boundary

**Status:** source-branch macro derivations and arithmetic composition. The generalized suffix-preserving Lean lemmas have not yet been written and compiled. The long root trajectory below is conditional, not a certified runtime bound.

## Notation

Write
\[
D_n(c;T)=CR([0],0^{4n+5}++[c]++T),
\qquad D_n(c)=D_n(c;[]).
\]
Here `T` is a list of stack tokens, not a bit-string suffix.

The pinned #85 source is
`M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean`
at commit `3647718b5df22e1a61462dec0376bd204526285a`.

## Empty-tail remainder one

The corrected source `mode_CR` clause for left stack prefix `[1,0]` is essential:
\[
CR([1,0]++L,[2])
\longrightarrow
CR(L,[0,5]).
\]
This is five raw steps: the right output is
`[0] ++ bumpPairHead (bumpPairHead (bumpPairHead [2])) = [0,5]`.

Composing the fixed prefix, sweeps, and the 16-step general-tail branch with the untouched suffix `[5]` gives
\[
\boxed{D_n(1)\longrightarrow D_0(8n+7;[5])}
\]
with `8n+41` outer successors and `16n+111` raw steps.

| Phase | Outer successors | Raw steps | Endpoint |
|---|---:|---:|---|
| Fixed prefix | 8 | 21 | `EL([0,1],0^(4n+6)1)` |
| EL zero sweep | `4n+6` | `8n+12` | `EL(0^(4n+7)1,[1])` |
| EL positive | 1 | 1 | `DL(0^(4n+7)1,[0])` |
| DL zero | 1 | 6 | `EL([0,1]0^(4n+6)1,[])` |
| EL empty | 1 | 1 | `CR([0,1]0^(4n+6)1,[0])` |
| CR zero | 1 | 2 | `CR([1]0^(4n+6)1,[2])` |
| CR `1,0` | 1 | 5 | `CR(0^(4n+5)1,[0,5])` |
| CR zero sweep | `4n+5` | `8n+10` | `CR([1],[8n+10,5])` |
| CR one/empty | 1 | 6 | `EL([0],[0,8n+13,5])` |
| Fixed tail, preserving `[5]` | 16 | 47 | `D_0(8n+7;[5])` |
| **Total** | **`8n+41`** | **`16n+111`** | |

The final 16-step chain is the existing general-tail branch with an arbitrary untouched suffix appended to each intermediate right stack. A suffix-parameterized Lean lemma is still needed.

## Remainder one with suffix `[5]`

The next exceptional family has a different, still ordinary-stack path:
\[
\boxed{D_n(1;[5])\longrightarrow D_0(8n+11;[0,0,2])}
\]
with `8n+44` outer successors and `16n+119` raw steps.

The source-branch sequence is:

1. Fixed prefix (8 outer / 21 raw), preserving `[5]`.
2. EL zero sweep of `4n+6` zeros (`4n+6` outer / `8n+12` raw).
3. EL positive on head `1` (1 / 1).
4. DL zero (1 / 6), leaving EL with suffix `[5]`.
5. EL positive on head `5` (1 / 1), then DL positive on head `4` (1 / 4).
6. DR zero with left head `0`, right head `1` (1 / 4).
7. DR positive-positive (1 / 3), giving `CR(0^(4n+7)1,0^3 2)`.
8. CR zero sweep of `4n+7` zeros (`4n+7` outer / `8n+14` raw).
9. CR one/empty (1 / 6), giving `EL([0],[0,8n+17,0,0,2])`.
10. The 16-step general-tail branch, preserving `[0,0,2]`, yields `D_0(8n+11;[0,0,2])`.

No token-normalizer call occurs in this `T=[5]` transition.

## Conditional root continuation

Combining the existing #85 root/countdown dossier with the remainder-two reset, the two remainder-one maps above, suffix-preserving countdown, and the offset-six phase transitions
\[
E_n(c)=CR([0],0^{4n+6}++[c]),
\]
gives the following source-branch arithmetic path:

\[
\begin{aligned}
D_{1294}(1)
&\to D_0(10359;[5])
\to E_{3453}(5)
\to E_{3454}(2)
\to D_0(27653)\\
&\to D_{9217}(2)
\to D_0(73755)
\to D_{24585}(0)
\to D_0(196693)\\
&\to D_{65564}(1)
\to D_0(524519;[5])
\to D_{174839}(2;[5])
\to D_0(1398737)\\
&\to D_{466245}(2)
\to D_0(3729979)
\to D_{1243326}(1)
\to D_0(9946615;[5])\\
&\to D_{3315538}(1;[5])
\to D_0(26524315;[0,0,2]).
\end{aligned}
\]

Additional source-branch maps used here:

- Suffix-preserving countdown:
  \[
  D_n(c;T)\to D_{n+1}(c-3;T),\quad c\ge3,
  \]
  with the same `8n+24` outer and `24n+69` raw cost as the empty-tail case.
- `E_n(5) -> E_(n+1)(2)`, cost `8n+26` outer and `24n+75` raw.
- `E_n(2) -> D_0(8n+21)`, cost `8n+46` outer and `40n+196` raw.
- `D_n(2;[5]) -> D_0(8n+25)`, using the same source token closure with `R3=[5]`, cost `8n+44` outer and `40n+186` raw.

**Conditional cumulative arithmetic:** `51,166,575,478,679` outer stack successors from the #85 seed and `153,499,683,790,849` raw TM steps from blank, ending at
\[
D_0(26,524,315;[0,0,2]).
\]
These totals are not a certified runtime bound until the suffix-preserving lemmas and every reset composition are formalized and checked.

## Next unresolved token-normalizer input

Since
\[
26,524,315=3\cdot8,841,438+1,
\]
the next suffix-preserving countdown leads to `D_(8,841,438)(1;[0,0,2])`. Its DL-right-one branch enters
\[
\operatorname{tok\_DR}([2,0],[],0^3 1 0^{4n+6}1),
\qquad n=8,841,438.
\]

The pinned source lemmas give the initial reduction
\[
\begin{aligned}
\operatorname{tok\_DR}([2,0],[],0^3 1 0^{4n+6}1)
&\to \operatorname{tok\_DR}([2,1,1,1,0],[],1 0^{4n+6}1)\\
&\to \operatorname{tok\_CR}([1^5,0],[],0^{4n+7}1)\\
&\to \operatorname{tok\_CR}([8n+15,1^4,0],[],[1])\\
&\to \operatorname{tok\_EL}([8n+15,1^4,0],[],0^3 1)\\
&\to \operatorname{tok\_DR}([2,8n+12,1^4,0],[],0^3 1).
\end{aligned}
\]

There is a reusable subtract-three cycle. For `x >= 3`,
\[
\operatorname{tok\_DR}([2,x,1^4,0],[],0^r1)
\to
\operatorname{tok\_DR}([2,x-3,1^4,0],[],0^{r+4}1),
\]
with raw cost `6r+35`: `r` applications of `tok_DR_zero`, one `tok_DR_1_nil_28`, `r+1` applications of `tok_EL_1`, and one `tok_EL_add3`.

Here `8n+12=70,731,516` is divisible by 3, so the cycle reaches the zero-remainder branch after `23,577,172` iterations, with `r=94,308,691`. The subsequent `tok_EL_0_cons` transition changes the K-tail and is the next token-normalizer case to resolve. Do not extrapolate the simple subtract-three cycle through that branch.

## Proof-script caveat

Agent 24's source audit found an off-by-one endpoint mismatch in the shared draft `root_countdown_prefix`: after the DL-positive h4, h5 must be `root_countdown_dr_zero_step [] ((0,0)::tail)`, and h6 must start from `(1,0)::(0,0)::(0,0)::tail`. The D2 appendix now contains a local corrected suffix-preserving prefix helper and no longer calls the flawed upstream theorem. The shared dossier should be patched separately.

Nothing here belongs in `results/`: these are intermediate derivations and uncompiled proof drafts. No nonhalting conclusion, halting-time theorem, exact BB(6) value, or universal upper bound is established.
