# The missing DR right-head-one token closure: a candidate blank-root nonhalting cycle

**Status:** source-derived recurrence and 1,000,000-successor computational check. The recurrence has not yet been formalized as a new Lean theorem in this repository. Treat the nonhalting conclusion as a proof target, not an accepted result.

## Pinned source and the branch error

The relevant external source is Google DeepMind cryptids, commit
[3647718b5df22e1a61462dec0376bd204526285a](https://github.com/google-deepmind/cryptids/tree/3647718b5df22e1a61462dec0376bd204526285a):

- #490 wrapper: BusyBeaver/BB6/Accelerations/M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean
- transported #85 source: BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean

The #490 wrapper's ClosedStackSystem.mirror swaps the arguments passed to the #85 evalStackCfg; the #85 evalStackCfg itself swaps the arguments when constructing cfg_DR_n_n. The two swaps cancel. Thus the seven-step blank-root entry in the #490 wrapper is the #85-oriented state

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

The old root prefix, corridor trace, and root-reachability claims built on that transition need recomputation. The standalone 76-step CR growth identity is a separate claim and need not be discarded solely for this reason; its connection to the blank root is what fails.

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

## Blank-root consequence, conditional on formalizing the composition

The #490 wrapper's init_reaches_nontrivial proves that the blank initial configuration reaches the DR seed in 7 raw steps. Composing the 19-step first closure with the recurrence gives, for every n≥0,

\[
  \mathrm{init}([])
  \xrightarrow{26+36n\ \mathrm{raw\ steps}}
  \mathrm{CR}([0,0,1],[1+5n]).
\]

These times are unbounded. A Lean proof of the first closure and the parameterized 36-step recurrence would therefore prove that this particular six-state machine does **not** halt from its blank start. That would eliminate this #490 blank-root candidate; it would not determine BB(6).

## Independent computational check

A source-equivalent persistent-list interpreter with the DR token condition corrected from b === 0 to b <= 1 was executed for 1,000,000 outer successors from DR([0,0],[1]). It returned

CR(L=[0,0,1], R=[714286])

with 142,858 DR token closures and no halting branch. This agrees with the recurrence: one initial closure followed by 142,857 seven-successor cycles, each adding 5 to the right counter. This is computational corroboration, not a substitute for the Lean proof.

The root trace previously reported from the b === 0 simulator (including the 21,810 token event and its later 76-step growth connection) is not evidence about the pinned source orbit. Recompute from the corrected branch before pursuing any root-to-cylinder or root-to-growth claim.

## Formalization target

Add a source-context Lean theorem for the parameterized 36-step recurrence, then compose it with the 7-step #490 root entry and the 19-step first closure. Keep the proof tied to the pinned #85/#490 source definitions and audit the exported theorem's axioms. Do not promote this note to results/ until the theorem is compiled and its source correspondence is explicit.
