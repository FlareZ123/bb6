# Cryptid D: source-local remainder-two closure

**Status:** source-lemma proof construction and an uncompiled Lean append draft. This is an intermediate result, not a compiled theorem and not a blank-root nonhalting proof.

The shared root-countdown dossier defines
\[
D_n(c)=CR([0],0^{4n+5}++[c]).
\]
Agent 12's source-branch recurrences already establish the countdown
\(D_n(c)\to D_{n+1}(c-3)\) for \(c\ge3\), and the zero reset
\(D_n(0)\to D_0(8n+13)\). See
[RootCountdownReset.md](../agent12-cryptid-root-invariant/RootCountdownReset.md).

This dossier supplies the missing source-lemma construction for
\[
D_n(2)\longrightarrow D_0(8n+19).
\]
The source-local Lean fragment is
[RootRemainderTwoToken.append.lean](RootRemainderTwoToken.append.lean).
It must be appended to the pinned #85 source module after
[RootCountdownSweep.append.lean](../agent12-cryptid-root-invariant/RootCountdownSweep.append.lean).
The fragment is intentionally marked uncompiled: the local shell/Python
boundary currently fails before executing even trivial commands, and the
repository's guidance forbids using CI as a substitute for local preflight.

## Exact token-normalizer route

Put \(m=4n+7\). The DL right-head-one branch takes four primitive TM steps
to
\[
\operatorname{tok\_DR}([2,0],[],0^m++[1]).
\]
The exact private source lemmas then give
\[
\begin{aligned}
\operatorname{tok\_DR}([2,0],R_3,0^m1)
&\xrightarrow{\operatorname{tok\_DR\_zero}^{m}}
  \operatorname{tok\_DR}([2,1^m,0],R_3,[1])\\
&\xrightarrow{\operatorname{tok\_DR\_1\_nil\_28}}
  \operatorname{tok\_EL}([1^{m+1},0],R_3,[0,0,0,1])\\
&\xrightarrow{\operatorname{tok\_EL\_1}^{m+1}}
  \operatorname{tok\_EL}([0],R_3,0^{m+4}1)\\
&\xrightarrow{\operatorname{tok\_EL\_exit\_zero}}
  CR(0^{m+4}1,\operatorname{bumpPairHead}(R_3)).
\end{aligned}
\]
For this reset, \(R_3=[]\), and the pinned definition gives
\(\operatorname{bumpPairHead}([])=[0]\). Thus the token endpoint is
\[
CR(0^{4n+11}1,[0]),
\]
not a right stack headed by 1.

The token subroutine costs
\[
4m+28+2(m+1)+1=6m+31
\]
primitive steps. Including the four-step DL entry gives
\(6m+35=24n+77\) primitive steps for the one outer stack successor.

## Full remainder-two phase decomposition

| Phase | Outer successors | Primitive steps | Endpoint |
|---|---:|---:|---|
| Fixed prefix | 8 | 21 | \(EL([0,1],0^{4n+6}2)\) |
| EL-zero sweep | \(4n+6\) | \(8n+12\) | \(EL(0^{4n+7}1,[2])\) |
| EL-positive | 1 | 1 | \(DL(0^{4n+7}1,[1])\) |
| DL/token closure | 1 | \(24n+77\) | \(CR(0^{4n+11}1,[0])\) |
| CR-zero sweep | \(4n+11\) | \(8n+22\) | \(CR([1],[8n+22])\) |
| CR-one/empty-tail | 1 | 6 | \(EL([0],[0,8n+25])\) |
| Fixed general tail | 16 | 47 | \(D_0(8n+19)\) |
| **Total** | **\(8n+44\)** | **\(40n+186\)** | |

The token phase is composed from the pinned source's tok_DR_zero,
tok_DR_1_nil_28, tok_EL_1, and tok_EL_exit_zero lemmas. The Lean
append also composes the existing root_countdown_prefix,
root_countdown_cr_zero_sweep_singleton,
root_countdown_cr_one_empty_step, and
root_countdown_general_tail helpers into root_countdown_two_reset.

## Root-connected consequence, conditional on compilation

The source-branch chain in Agent 12's dossier reaches \(D_{65}(2)\) after
21,535 outer successors from the #85 seed and raw TM time 64,018 from
blank. If root_countdown_two_reset compiles in the pinned source module,
then the next checkpoint is
\[
D_{65}(2)\to D_0(539)
\]
after 564 more outer successors and 2,786 more primitive steps: cumulative
22,099 outer successors from the #85 seed and raw time 66,804 from blank.

The existing countdown theorem would then give the conditional continuation
\[
D_0(539)\to D_{179}(2)\to D_0(1451)
\to D_{483}(2)\to D_0(3883)\to D_{1294}(1).
\]
The remainder-one state \(D_{1294}(1)\) is not resolved here. In particular,
this document does not establish an infinite orbit, nonhalting, a BB(6)
value, or a universal upper bound.

All material remains in im-results/; nothing here qualifies for results/.
