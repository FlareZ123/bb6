# Source-accurate D-countdown sweep recurrence

**Status (2026-11-22):** This is the surviving, source-accurate part of the earlier root-growth investigation. It is a branch-level derivation and bounded replay, not yet a compiled Lean theorem. It does **not** establish that the blank-root trajectory reaches any (D_n(c)) state. The former 1,131,748-step root-to-growth route and 76-step growth macro are withdrawn because their projected CR 1,0 / 1,1 / 1,≥2 branches were mistranscribed; see [the critical correction](../../communications/broadcast/20261122T0813Z_agent12-critical-CR-branch-withdrawal.md).

## Statement

Use the pinned #85 stack coordinates and first-coordinate notation, with (0=(0,0)), (1=(1,0)). Define

[
D_n(c)=CR(L=[0],R=0^{4n+5}++[c]).
]

For every (n\ge0) and (c\ge3), the ordinary source clauses give the projected recurrence

[
D_n(c)\;\longrightarrow^{\,8n+24\,}\;D_{n+1}(c-3),
]

with raw machine cost

[
24n+69.
]

The recurrence uses only the CR-left-zero and CR-empty branches; it does not use any of the mistranscribed CR-left-one branches.

## Exact phase decomposition

| Phase | Outer successors | Raw TM steps | Start → endpoint |
|---|---:|---:|---|
| Fixed prefix | 8 | 21 | (CR([0],0^{4n+5}++[c])\to EL([0,1],0^{4n+6}++[c])) |
| EL zero sweep | (4n+6) | (8n+12) | (EL([0,1],0^{4n+6}++[c])\to EL(0^{4n+7}++[1],[c])) |
| EL-positive then DL-positive | 2 | 5 | (EL(0^{4n+7}++[1],[c])\to DR(0^{4n+7}++[1],[1,c-3])) |
| DR zero sweep | (4n+7) | (16n+28) | (DR(0^{4n+7}++[1],[1,c-3])\to DR([1],[1]++0^{4n+7}++[c-3])) |
| Final DR-positive/positive | 1 | 3 | (DR([1],[1]++0^{4n+7}++[c-3])\to D_{n+1}(c-3)) |
| **Total** | **(8n+24)** | **(24n+69)** | |

The fixed eight-successor prefix has raw costs (2,2,1,4,4,1,1,6):
1. CR left head 0;
2. CR empty left;
3. EL positive right head 3;
4. DL right head 2;
5. DR left head 0 / right head 1;
6. DR empty left;
7. EL right head 1;
8. DL right head 0.

The first two CR clauses are the pinned source `mode_CR_n_n_closed` lines 905–916. The EL/DL/DR clauses are the ordinary branches of the corresponding pinned mode closures: EL positive (1), DL positive (4), DR left-zero/right-one (4), DR empty-left (1), and DL right-zero (6).

After the prefix, the EL sweep repeats the source EL-right-zero branch (`execute 2`) (4n+6) times. The next EL-positive and DL-positive branches cost (1+4). The DR sweep repeats the source DR-left-zero/right-one branch (`execute 4`) (4n+7) times. The final DR-positive/positive branch costs 3.

The arithmetic is

[
8+(4n+6)+2+(4n+7)+1=8n+24,
]

[
21+2(4n+6)+5+4(4n+7)+3=24n+69.
]

## Formalization route

Only three components are needed:

1. A fixed eight-branch prefix, proved by composing the source CR/EL/DL/DR ordinary branches.
2. An inductive EL-zero sweep, using the one-step source equation (EL(L,0::R)\to EL(0::L,R)) with `execute 2`.
3. An inductive DR-zero sweep, using (DR(0::L,1::R)\to DR(L,1::0::R)) with `execute 4`.

The sweep lemma draft is in [Agent 12 → Agent 32 communication](../../communications/agent32/20261122T0810Z_agent12-countdown-sweep-lean-draft.md). It is written for the #85 source module. Once proved there, lift the resulting `ReachesPlus` path to #490 with pinned `Stack.lean`'s `reachesPlus_mirrorCfg` (lines 359–365); the evaluator argument reversals cancel and the #490 blank-entry theorem supplies the same #85 coordinates (DR([0,0],[1])).

## Reproduction and scope

A source-transcribed replay using the corrected CR clauses and ordinary EL/DL/DR clauses checked (n\in\{0,1,2,5\}) and (c\in\{3,4,7\}). Every run reached the stated endpoint and had raw cost (24n+69). This is a finite computation, not a proof.

The earlier shared-corridor derivation, reset/c=1 corridor/H-padding/H-base path, root macro indices, and 76-step DR/G/B insertion all depended on the incorrect projected CR 1,0 / 1,1 / 1,≥2 rules and are not supported by this file. The blank-root continuation beyond the independently checked first raw steps must be recomputed. No halting or nonhalting conclusion for D0, and no BB(6) value, follows.
