# Cryptid D: source-local root trajectory

**Status:** intermediate source-branch derivations and uncompiled Lean append drafts. No theorem in this dossier has passed Lean compilation.

The shared #85 root-countdown dossier defines
\[
D_n(c)=CR([0],0^{4n+5}++[c]).
\]
Its existing source-branch recurrences include the countdown
\[
D_n(c)\to D_{n+1}(c-3),\quad c\ge3,
\]
and the zero reset
\[
D_n(0)\to D_0(8n+13).
\]
See [RootCountdownReset.md](../agent12-cryptid-root-invariant/RootCountdownReset.md).

## Remainder two

The missing remainder-two macro is
\[
D_n(2)\longrightarrow D_0(8n+19),
\]
with `8n+44` outer successors and `40n+186` raw steps. The source-local Lean construction is in [RootRemainderTwoToken.append.lean](RootRemainderTwoToken.append.lean), to be appended after [RootCountdownSweep.append.lean](../agent12-cryptid-root-invariant/RootCountdownSweep.append.lean) in the pinned #85 module.

The token closure is composed from the pinned `tok_DR_zero`, `tok_DR_1_nil_28`, `tok_EL_1`, and `tok_EL_exit_zero` lemmas. The endpoint is `CR(0^(4n+11)1,[0])`, because `bumpPairHead([])=[0]`. The appendix contains inductive sweep helpers and the full `root_countdown_two_reset` composition.

## Remainder one and suffix transitions

[RootRemainderOneTail.md](RootRemainderOneTail.md) derives two further maps:

\[
D_n(1)\to D_0(8n+7;[5]),
\]
with `8n+41` outer / `16n+111` raw steps, and
\[
D_n(1;[5])\to D_0(8n+11;[0,0,2]),
\]
with `8n+44` outer / `16n+119` raw steps.

The same note gives the conditional arithmetic continuation from (D_{1294}(1)) to
\[
D_0(26,524,315;[0,0,2]).
\]
This uses suffix-preserving countdown, the offset-six transitions, and a remainder-two token closure with suffix `[5]`; those generalized lemmas are not yet formalized.

## Conditional root trajectory

Conditional on the full source-branch composition and its future formalization, the trajectory reaches
\[
D_0(26,524,315;[0,0,2])
\]
after `51,166,575,478,679` outer stack successors from the #85 seed and `153,499,683,790,849` raw TM steps from blank. Do not treat this as a certified lower bound until the generalized suffix lemmas and every reset composition are proved in Lean.

The next countdown reaches `D_(8,841,438)(1;[0,0,2])`. Its DL-right-one branch enters
\[
\operatorname{tok\_DR}([2,0],[],0^3 1 0^{4n+6}1),
\qquad n=8,841,438,
\]
where the source token rules admit a subtract-three cycle. The zero-remainder `tok_EL_0_cons` case is now the main unresolved token-normalizer boundary.

## Proof and scope caveats

Agent 24 found an off-by-one mismatch in the shared `root_countdown_prefix` proof: after h4, h5 must use `root_countdown_dr_zero_step [] ((0,0)::tail)`, and h6 must start from `(1,0)::(0,0)::(0,0)::tail`. The D2 appendix now supplies a local corrected suffix-preserving prefix helper and no longer calls the flawed upstream theorem. The shared dossier should be patched separately.

All material remains in `im-results/`; nothing here qualifies for `results/`. No nonhalting result, halting-time theorem, exact BB(6) value, or universal upper bound is established.
