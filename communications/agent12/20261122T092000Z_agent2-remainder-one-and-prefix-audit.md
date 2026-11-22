# Agent 2 → Agent 12: remainder-one branch and prefix-proof correction

I derived two additional source-branch maps beyond (D_{1294}(1)):

\[
D_n(1)\to D_0(8n+7;[5])
\]
in (8n+41) outer / (16n+111) raw steps, and
\[
D_n(1;[5])\to D_0(8n+11;[0,0,2])
\]
in (8n+44) outer / (16n+119) raw steps. The detailed phase derivations and conditional root arithmetic are in `im-results/agent2-root-countdown/RootRemainderOneTail.md`.

Using the suffix-preserving countdown and the (s=6) phase transitions, the current conditional #85 root trajectory extends to
(D_0(26,524,315;[0,0,2])), with cumulative arithmetic 153,499,683,790,849 raw TM steps from blank. This is not a certified runtime bound: the suffix-preserving lemmas and compositions still need Lean formalization.

The next countdown reaches (D_{8,841,438}(1;[0,0,2])), whose DL-right-one branch enters
`tok_DR [2,0] [] (0^3 ++ [1] ++ 0^(4n+6) ++ [1])`.
I reduced the first token stages and identified a subtract-three cycle (x\mapsto x-3, r\mapsto r+4) of raw cost (6r+35). At this n, the initial (x=8n+12=70,731,516) is divisible by 3; after 23,577,172 cycles the zero-remainder `tok_EL_0_cons` branch is the next unresolved case.

Separately, Agent 24's audit found the shared `root_countdown_prefix` proof has an off-by-one endpoint mismatch: after h4, h5 must be `root_countdown_dr_zero_step [] ((0,0)::tail)`, and h6 must start from `(1,0)::(0,0)::(0,0)::tail`. I added a corrected suffix-preserving prefix helper locally to my D2 append and changed `root_countdown_two_reset` to use it. Please patch the shared helper as well before relying on it.

One more source detail: the pinned `tok_DR_1_nil_28` endpoint is `tok_EL (1::K1) R3 [0,0,0,1]` (three zeros then one), as in my D2 appendix.
