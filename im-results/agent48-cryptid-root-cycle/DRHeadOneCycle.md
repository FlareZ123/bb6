# Historical analysis (withdrawn): incorrect DR right-head-one token interpretation

**Status:** source-derived recurrence and 1,000,000-successor computational check. The recurrence has not yet been formalized as a new Lean theorem in this repository. Treat the nonhalting conclusion as a proof target, not an accepted result.

**Status: WITHDRAWN.** The central source-branch interpretation in this report is incorrect: it applies the `mode_DL_0_n_closed` right-head-one token branch to `mode_DR_n_n_closed`. In the pinned source, `mode_DR` splits right-head 0 from positive heads; the r1=1,a1=0 case is the ordinary four-step DR transition. Only `mode_DL` has the 0/1/≥2 split whose r1=1 case calls `tok_DR_2_0_closed`.

For the #490 blank-root seed, the two argument swaps in `evalStackCfg` and `ClosedStackSystem.mirror` cancel, so the #85-oriented state is `DR(L=[0,0],R=[1])`. It takes the ordinary four-step edge to `DR([0],[1,0])), not the claimed 19-step token closure. The last edge of the proposed 36-step recurrence is wrong for the same reason. The `b <= 1` simulator replay and its claimed 1,000,000-successor endpoint are not source-faithful.

The exact source audit and the recovered source-transcribed root countdown/growth candidate are documented in [Agent 12's ModeDRBranchAudit](../agent12-cryptid-root-invariant/ModeDRBranchAudit.md) and [RootCountdownGrowth](../agent12-cryptid-root-invariant/RootCountdownGrowth.md). This file is preserved below only as the historical record of the mistaken interpretation; none of its 19-step/36-step conclusions should be used.

---


## Pinned source and the branch error

The relevant external source is Google DeepMind cryptids, commit
[3647718b5df22e1a61462dec0376bd204526285a](https://github.com/google-deepmind/cryptids/tree/3647718b5df22e1a61462dec0376bd204526285a):

- #490 wrapper: BusyBeaver/BB6/Accelerations/M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean
- transported #85 source: BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean

The #490 wrapper's ClosedStackSystem.mirror swaps the arguments passed to the #85 evalStackCfg; the #85 evalStackCfg itself swaps the arguments when constructing each of cfg_CR_n_n, cfg_EL_n_n, cfg_DL_0_n, and cfg_DR_n_n. The two swaps cancel in all four modes, so the wrapper carries the same L,R pair lists through the entire #85 stack recurrence. Thus the seven-step blank-root entry in the #490 wrapper is the #85-oriented state

\[
  \mathrm{DR}(L=[0,0],R=[1]).
\]

The decisive source split is mode_DR_n_n_closed in the #85 file (around lines 1008–1064). Once both lists are nonempty, it splits the first coordinate r1 of the right head twice:

- r1=0: token closure;
- r1=1: **also token closure**;
- r1≥2: ordinary DR/CR stack transition.

In the r1=1,a1=0 case, the source explicitly calls tok_DR_2_0_closed R3 (L3.map Prod.fst). The texecute 4 in this branch is only the prefix from cfg_DR_n_n to the inner tok_DR [2,0] configuration; it is composed with the token closure. It is not the complete stack successor.

The current repository simulators instead test only b === 0 / b == 0 before taking the ordinary DR branch. They therefore mishandle the source case R.head=1,L.head=0. This affects:

- im-results/agent12-cryptid-root-invariant/fast_root_stack_sim.js
- im-results/agent12-cryptid-root-invariant/verify_root_corridor_macro.js
- im-results/agent32-cryptid-padding/stack_system_sim.py

The old root prefix, corridor trace, and root-reachability claims built on that transition need recomputation. Replaying the H-phase CR 76-step macro and the DR/G/B 76-step macro with the corrected branch also fails to reach either claimed endpoint; each encounters the newly required DR token closure. The triangular D_n(c) countdown checks likewise fail for the tested n=0,...,6 and c=3,4,5,10,540. These are not source-valid macro identities under the pinned mode clauses.

## Exact first source closure

At the blank-root stack seed, L=[0,0], R=[1], so a1=0,r1=1. The source uses tok_DR_2_0_closed with R3=[], L3=[0].

The raw path is explicit:

| Source step | Raw steps | Configuration |
|---|---:|---|
| mode_DR prefix | 4 | tok_DR([2,0], [], [0]) |
| tok_DR_zero | 4 | tok_DR([2,1,0], [], []) |
| tok_DR_nil_8 | 8 | tok_EL([1,0], [], [0,1]) |
| tok_EL_1 | 2 | tok_EL([0], [], [0,0,1]) |
| tok_EL_exit_zero | 1 | CR([0,0,1], [1]) |

Hence
\[
  \mathrm{DR}([0,0],[1])
  \xrightarrow{19\ \mathrm{raw\ steps}}
  \mathrm{CR}([0,0,1],[1]).
\]

This uses the pinned source lemmas tok_DR_zero, tok_DR_nil_8, tok_EL_1, and tok_EL_exit_zero; no general token-normalizer conjecture is needed for this input.

## A seven-successor, 36-raw-step recurrence

For every c≥1, the source mode clauses give the following chain:

| Outer successor | Source stack state | Raw steps |
|---:|---|---:|
| 0 | CR([0,0,1], [c]) | — |
| 1 | CR([0,1], [c+2]) | 2 |
| 2 | CR([1], [c+4]) | 2 |
| 3 | EL([0], [0,c+7]) | 6 |
| 4 | EL([0,0], [c+7]) | 2 |
| 5 | DL([0,0], [c+6]) | 1 |
| 6 | DR([0,0], [1,c+4]) | 4 |
| 7 | CR([0,0,1], [c+5]) | 19 |

The final 19-step DR closure is the same source token branch as above, now with R3=[c+4]. Its token subpath is unchanged except that tok_EL_exit_zero increments the right context from [c+4] to [c+5].

Thus the proposed exact recurrence is
\[
  \mathrm{CR}([0,0,1],[c])
  \xrightarrow{36\ \mathrm{raw\ steps}}
  \mathrm{CR}([0,0,1],[c+5])
  \qquad(c\ge1).
\]

The 36 steps are 2+2+6+2+1+4+19. Each ordinary segment is one of the explicit execute branches in mode_CR_n_n_closed, mode_EL_n_n_closed, or mode_DL_0_n_closed; the final segment is the r1=1,a1=0 tok_DR_2_0_closed branch.

The cycle passes through CR(L=[1],R=[c+4]) at its third outer state. Thus the former global left-stack invariant L∈Z1=0*(ε|1) is not valid for this orbit. The appropriate observed mode-dependent class is L∈Z1 except for this CR(L=[1]) state; the shared fast simulator's invariant checker has been adjusted accordingly.

## Blank-root consequence, conditional on formalizing the composition

The #490 wrapper's init_reaches_nontrivial proves that the blank initial configuration reaches the DR seed in 7 raw steps. Composing the 19-step first closure with the recurrence gives, for every n≥0,

\[
  \mathrm{init}([])
  \xrightarrow{26+36n\ \mathrm{raw\ steps}}
  \mathrm{CR}([0,0,1],[1+5n]).
\]

These times are unbounded. The #490 wrapper is a state relabelling plus tape reflection of #85, so the same raw-step reachability chain transfers to its target machine. A Lean proof of the first closure and the parameterized 36-step recurrence would therefore prove that this particular six-state machine does **not** halt from its blank start. That would eliminate this #490 blank-root candidate; it would not determine BB(6).

## Independent computational check

A source-equivalent persistent-list interpreter with the DR token condition corrected from b === 0 to b <= 1 was executed for 1,000,000 outer successors from DR([0,0],[1]). It returned

CR(L=[0,0,1], R=[714286])

with 142,858 DR token closures and no halting branch. This agrees with the recurrence: one initial closure followed by 142,857 seven-successor cycles, each adding 5 to the right counter. This is computational corroboration, not a substitute for the Lean proof.

The root trace previously reported from the b === 0 simulator (including the 21,810 token event and its later 76-step growth connection) is not evidence about the pinned source orbit. Recompute from the corrected branch before pursuing any root-to-cylinder or root-to-growth claim.


## Recheck of the old countdown and growth claims

The source-corrected interpreter was also applied to the other published projected macros. These checks are falsifications of the old simulator's claimed endpoints, not proofs of a replacement trajectory:

- The D_n(c) countdown test fails for every tested n=0,...,6 and c in {3,4,5,10,540}; for example, the old n=0,c=3 endpoint is not reached after 24 successors.
- The CR H-phase 76-step test from CR([1,0],P++B++U) does not reach CR([1,0],P++B++B++U); the corrected path invokes a DR token closure and ends in a different state.
- The DR/G/B 76-step test from DR(G,[1]++B++T) also fails its former endpoint after the corrected source branch.

The updated regression harness is im-results/agent12-cryptid-root-invariant/verify_root_corridor_macro.js. It now tests the root cycle and asserts that the old endpoints do not survive. The separate H-phase and DR/G/B identities must be rederived from the pinned source before reuse.

## Formalization target

Add a source-context Lean theorem for the parameterized 36-step recurrence, then compose it with the 7-step #490 root entry and the 19-step first closure. Keep the proof tied to the pinned #85/#490 source definitions and audit the exported theorem's axioms. Do not promote this note to results/ until the theorem is compiled and its source correspondence is explicit.
