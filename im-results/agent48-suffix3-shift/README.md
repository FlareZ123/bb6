# Universal ternary suffix shift in Cryptid D

**Research status:** exact transition law derived from the pinned original #85 source's CR/EL/DL/DR clauses, with standalone source-local **uncompiled** Lean proof drafts. The same shift is drafted for **every arbitrary finite further stack tail**. These are candidate infinite-family reductions, not yet accepted original-machine Lean theorems or a blank-tape decision.

Define the source-coordinate family

\[
Q(n,t)=\operatorname{cfg\_CR\_n\_n}
([ (0,0) ],\, 0^{4n+5}++[(0,0),(t,0)]).
\]

Unlike the earlier isolated suffix-[5] calculation, the following has **no restriction on** \(t\ge 0\):

\[
\boxed{Q(n,t+3)\longrightarrow^+ Q(n+1,t).}
\tag{1}
\]

## Source-rule derivation

Starting at \(Q(n,t+3)\), the exact corrected eight-successor CR/EL/DL/DR prefix returns to EL with left stack \([0,1]\) and right stack \(0^{4n+6}[0,t+3]\). Sweep \(4n+7\) right zeros in EL to get \(\operatorname{EL}(0^{4n+8}1,[t+3])\). Since \(t+3\ge3\), take EL-positive then DL-positive, yielding \(\operatorname{DR}(0^{4n+8}1,[1,t])\). Sweep \(4n+8\) left zeros in DR, then apply DR-positive-positive to reach

\[
\operatorname{CR}([0],0^{4n+10}[t])
=Q(n+1,t).
\]

Every transition is an explicitly applicable nonhalting original-source clause; the argument does **not** use the generic existential token-closure theorem or an inferred root path. Primitive-step costs of the constituent clauses give:

\[
\boxed{8n+26\text{ outer stack successors},\qquad
24n+75\text{ raw TM steps}.}
\tag{2}
\]

Repeating (1) \(k\ge1\) times yields

\[
\boxed{Q(n,t+3k)\longrightarrow^+Q(n+k,t)}
\tag{3}
\]

with (by arithmetic summation of source clauses)

\[
\boxed{8nk+4k^2+22k\text{ outer successors},\qquad
24nk+12k^2+63k\text{ raw steps}.}
\tag{4}
\]

This collapses the entire unbounded singleton suffix \(t\) to the three residues \(0,1,2\pmod3\). It does **not** decide the three residual families. The nontrivial residual-one branch remains the main obstacle.

## Independent bounded source-clause replay

A V8 accelerated interpreter directly implementing the upstream four stack-mode source clauses, without token substitutions, reaches \(Q(n+2,t)\) from \(Q(n,t+6)\) for every tested \(n=0,1,2\) and \(t=0,1,2,3,4,5,6,7,11,20\). Every test terminated **before any token branch** with exactly \(16n+60\) outer successors and \(48n+174\) raw primitive steps, as predicted by (4). This is supporting finite computational evidence, not a substitute for source-level proof acceptance.

## Formal proof and verification boundary

[RootSuffixThreeShift.append.lean](RootSuffixThreeShift.append.lean) defines \`s3D\`, eleven source-local small-step lemmas, \`s3_prefix\` with the crucial corrected DR-zero endpoint, and states \`s3_universal_suffix_shift\` plus \`s3_iterated_suffix_shift\` in the original module's \`ReachesPlus target\` semantics. It does **not** depend on the much larger pending RootCountdownSweep/RootRemainderTwoToken append chain. Insert it before the final \`end BusyBeaver.M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA\` of the DeepMind [pinned source](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean). No imported research append is required.

The file has **not yet compiled** because the local shell returned \`ClientError\` at tool entry. A targeted source-exact manual Lean CI compile or equipped local collaborator is needed. The strongest acceptable certificate must include the complete original module closure, this appended file and transitive axiom profiles without \`sorryAx\`. The raw-step formulas are derived from the original source's exact counts but would still need formal counted-step composition for kernel-backed numerical claims. Until accepted, no result should be promoted from \`im-results/\` to \`results/\`.

## Consequences and overlap

The earlier [suffix-[5] reduction](../agent48-suffix5-reset/README.md) is now the \(t=2\) instance of (1) followed by the residual-two token closure \(Q(n,2)\to D_0(8n+21)\), giving \(Q(n,5)\to D_0(8n+29)\). The original suffix-[5] Lean append can be simplified to the present universal lemma plus the residual-two proof, once both are accepted.

Source-clause replay also suggests the residual-zero family \(Q(n,0)\to D_0(8n+15)\) with \(8n+43\) outer and \(16n+109\) raw steps, and the residual-two family \(Q(n,2)\to D_0(8n+21)\) with \(8n+46\) outer and \(40n+196\) raw steps. These latter laws require separate original-source formalization. If they are accepted, the entire congruence classes \(t\equiv0,2\pmod3\) admit explicit \(D_0\) reset formulas; \(t\equiv1\pmod3\) requires a different token analysis.

Combining the source-derived shift with these still-unaccepted residual base cases produces the conditional general formulas, for every (kge0):

\[
\begin{aligned}
Q(n,3k)&\to^+D_0(8(n+k)+15),\\
Q(n,3k+2)&\to^+D_0(8(n+k)+21).
\end{aligned}
\]

The proposed primitive-step costs, including the residual endpoint, are respectively (24nk+12k^2+79k+16n+109) and (24nk+12k^2+103k+40n+196). These are **clause-derived** and have not passed counted-run formalization. The corresponding outer successor counts are (8n(k+1)+4k^2+30k+43) and (8n(k+1)+4k^2+30k+46). These formulas should not be mistaken for global machine runtime bounds.

[RootSuffixWordShift.append.lean](RootSuffixWordShift.append.lean) independently drafts the stronger (Q(n,t+3;T)\to^+Q(n+1,t;T)) and its iterates for an **arbitrary finite pair-stack tail** (T). The source path never inspects the tail. This file is not compiled.

In particular, the conditional root state \(Q(428725269581,5)\) reduces to \(Q(428725269582,2)\), then conditionally to \(D_0(3429802156677)\). This is not an unconditional blank-tape halting or nonhalting decision.
