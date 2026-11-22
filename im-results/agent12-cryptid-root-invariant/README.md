# Historical root stack experiment: superseded by the DR head-one correction

**Status: WITHDRAWN as a source orbit.** The simulator omitted the pinned source's DR right-head-one token branch. The root trajectory, countdown, and growth claims below are historical outputs of the defective successor and must not be used as source evidence. See [the corrected DR head-one analysis](../agent48-cryptid-root-cycle/DRHeadOneCycle.md) for the source-derived 19-step root closure and candidate 36-step nonhalting recurrence.

## Superseded experiment record (not source-valid)

The following sections preserve the earlier experiment for traceability only. Their root indices, macro states, finite-prefix invariant, and growth connection are invalidated by the missing DR r1=1 token branch.

## Experiment

The accelerated root seed is the #85-oriented stack configuration
\[
\mathrm{DR}(L=[0,0],R=[1]),
\]
entered at raw TM time 7. The persistent-list interpreter in
[fast_root_stack_sim.js](./fast_root_stack_sim.js) transcribes the four
outer mode rules and token normalizers in
[stack_system_sim.py](../agent32-cryptid-padding/stack_system_sim.py).
A source audit found and corrected a missing zero insertion in the EL
normalizer and two CR-token suffix errors. The correction is documented in
[TokenNormalizerCorrection.md](./TokenNormalizerCorrection.md).

A source-equivalent persistent-list recurrence was executed in the V8 runtime
for 1,000,000 macro-successor steps. It produced:

- no token-halting branch;
- no CR branch with left head at least 2;
- no closeTokCR invocation;
- exactly one closeTokDR invocation, at macro index 21,810;
- that invocation's input was \(0^{267} ++ [1]\), and its corrected output was
  \(\mathrm{CR}(L=0^{271} ++ [1],R=[1])\);
- 268 bounceDR calls and zero bounceCR calls;
- maximum left-list length 1,832, maximum right-list length 1,832,
  maximum entry 1,459, at most one nonzero entry in the left list, and at
  most two nonzero entries in the right list;
- throughout the trace, the left list remained in
  \(Z_1=0^*(\epsilon\mid1)\).

The corrected root continuation is:

| Macro index | State |
|---:|---|
| 21,810 | \(\mathrm{DL}(L=0^{267}1,R=[1])\), invoking the DR token closure |
| 21,811 | \(\mathrm{CR}(L=0^{271}1,R=[1])\) |
| 21,827 | \(\mathrm{CR}(L=0^{255}1,R=[33])\) |
| 21,926 | \(\mathrm{CR}(L=0^{156}1,R=[231])\) |
| 22,083 | \(\mathrm{EL}(L=[0],R=[0,546])\) |

At macro index 1,000,000 the corrected run was in mode DR, with
\(L=0^{1315}1\), right-list length 518, and right nonzero projection \([1,82]\). The previous report of a 154,446-entry
right stack and a terminal state in the CR mode came from the defective
normalizer and is withdrawn.

These are macro-successor counts, **not raw TM steps**. They are computational
evidence for the source-transcribed stack recurrence, not a proof that the
original TM runs forever. The checked-in Node script and regression harness
have been edited; the exact file was not run under Node/CI after the edits.
The local shell tool returned a ClientError, so the available V8 execution used
a direct source-equivalent transcription. The initial raw prefix to the
accelerated stack seed remains separate from these macro counts.

## Finite-prefix candidate invariant

The experiment checked the following predicate before every one of the
1,000,000 successor applications, without finding a counterexample. It is a
candidate for formalization, not yet an established invariant.

Write \(Z_1=0^*(\epsilon\mid1)\), and let \(\operatorname{firstNZ}(R)\)
be the first nonzero entry of \(R\), if any.

1. \(L\in Z_1=0^*(\epsilon\mid1)\): the left list is all zeros, optionally followed by one terminal 1.
2. \(R\) has at most two nonzero entries.
3. In mode DR, \(R\) is nonempty and its head is positive.
4. In mode EL:
   - if the head of \(R\) is 1, \(L\) begins with 0;
   - if \(\operatorname{firstNZ}(R)=2\), then \(L\in Z_1\);
   - if the head of \(R\) is 1 and the first nonzero entry of the tail of \(R\) is 2, then \(L\in\{\epsilon,[0]\}\).
5. In mode DL:
   - if the head of \(R\) is 0, \(L\) begins with 0;
   - if the head of \(R\) is 1, then \(L\in Z_1\);
   - if the head of \(R\) is 0 and the first nonzero entry of the tail of \(R\) is 2, then \(L\in\{\epsilon,[0]\}\).
6. In mode CR, if \(L\) begins with \([1,1]\) and the head of \(R\) is 1, then \(L\) with its first two entries removed belongs to \(Z_1\).

The exact predicate, including the finite lookahead conditions, the stronger
Z1 test, and the two-nonzero right-stack bound, is implemented by
`invariantFailures` in the JavaScript interpreter. The corrected trace
satisfies it for the first 1,000,000 macro successors. These conditions are
finite-prefix diagnostics, not an all-time invariant.

## Why this could matter

The first-million-step predicate explains why the observed finite prefix
avoids the two stack halting branches. It is not an all-time nonhalting
invariant: the later corrected root trajectory leaves Z1 and has an
unbounded number of nonzero right-stack entries, entering the growth family
described in RootCountdownGrowth.md.

For \(L\in Z_1\), the corrected DR token normalizer preserves \(Z_1\):
\(0^n\) maps to \(\mathrm{CR}(L=0^{n+1}1,R=\operatorname{bump}(r))\),
and \(0^n1\) maps to \(\mathrm{CR}(L=0^{n+4}1,R=\operatorname{bump}(r))\).
The observed \(0^{267}1\) input therefore returns
\(\mathrm{CR}(L=0^{271}1,R=[1])\). See
[TokenNormalizerCorrection.md](./TokenNormalizerCorrection.md).

In the first million macro successors, every DL state with right head 0 had
L=[0], and every EL state with right head 1 also had L=[0]. The one EL state
with right head 2 was immediately before the single token closure. These are
finite-prefix observations only: the later corrected root trajectory exits
Z1 and the two-nonzero right-stack bound. The countdown and growth macros,
rather than a global Z1 invariant, are now the priority proof targets.


## Counterexample-guided audit of the candidate

The finite-prefix predicate is not globally inductive. A small
counterexample already satisfies L in Z1, the two-nonzero right-stack bound,
and the current DL guard:

\[
\mathrm{DL}(L=[0,0],R=[0])
\longrightarrow
\mathrm{EL}(L=[0,1,0],R=[]).
\]

The successor leaves \(Z_1\). Thus the root-specific observation
\(\mathrm{DL}(R_0)\Rightarrow L=[0]\) is essential; the weaker condition
"\(L\) begins with zero" is insufficient.

More generally, one-step searches expose dependencies between the number of
leading zeros in \(R\), the first nonzero entry of its tail, and the regular
shape of \(L\). The next useful invariant should encode this relationship
with a small finite-state summary of the nonzero prefix of \(R\), rather than
adding unrelated implications one at a time.

The first million-step root prefix satisfies the checked predicate. The
later root-reachable growth phase violates both the Z1 and two-nonzero
right-stack bounds. Do not promote the finite-prefix observation to a
global invariant.


## Raw-state correspondence and first-branch audit

The four mode names are not four distinct target-machine states. In the base
#85 source, CR uses C, EL uses E, and both DL and DR use D with opposite head
orientations. Under the state permutation and tape mirror in the #490 wrapper,
the corresponding #490 raw states are:

- CR: state C, head-left;
- EL: state B, head-right;
- DL: state A, head-right (with the extra leading-zero side);
- DR: state A, head-left.

This is why the raw-prefix parser uses q2 for CR, q1 for EL, and q0 with
different head orientations for DL and DR.

The upstream mode_DR_n_n_closed source split also resolves the first root
branch: at DR(L=[0,0],R=[1]), both lists are nonempty, L.head=0 and R.head=1.
The source takes the four-step branch to DR(L=[0],R=[1,0]). The
tok_CR_1_0_closed branch instead requires R.head=0 and L.head>0. A statement
in ASectionStackEncoding.md about a first root-to-token checkpoint therefore
needs an explicit later macro/raw location or a different argument
orientation; Agent 32 was asked to reconcile it with the source cases.


## Closed form for the DR-token normalizer on Z1

The source-derived bounce rules give the following exact formulas for any
right context \(r\):

\[
\begin{aligned}
\operatorname{closeTokDR}(r,0^n)
  &= \mathrm{CR}(L=0^{n+1}1,\,R=\operatorname{bump}(r)),\\
\operatorname{closeTokDR}(r,0^n1)
  &= \mathrm{CR}(L=0^{n+4}1,\,R=\operatorname{bump}(r)).
\end{aligned}
\]

Indeed, bounceDR with initial accumulator \([0]\) maps \(0^n\) to
accumulator \([1^n,0]\) and right suffix \([1]\), and maps \(0^n1\) to
accumulator \([1^{n+1},0]\) and right suffix \([0,0,1]\). The corrected EL
normalizer applies tok_EL_1 once for every leading 1, prepending a zero each
time, before the final zero emits the CR state. Thus these closures preserve
\(Z_1\). The macro-21,810 event is the second case with \(n=267\) and empty
context \(r\).

The CR-token clauses were corrected too: the \([1,1]\) nil case returns
right suffix \([0,1]\), and the cons case returns \([0,c+2]++L_3\).
For the EL accumulator head \(v\ge3\), the existing bounceDR argument is
already correct: the source proof composes tok_EL_add3 with tok_DR_zero, which
consumes the leading zero before bounceDR begins. See
[TokenNormalizerCorrection.md](./TokenNormalizerCorrection.md) for the
source-level audit.


## Exact corridor macro family

[RootCorridorMacro.md](RootCorridorMacro.md) gives the source-audited corridor
identities for \(\mathrm{Corr}(r,c)=\mathrm{DR}(L=0^r1,R=[1,c])\): the
\(c\ge3\) decrement-by-three step, the \(c=0\) reset, the corrected
\(c=2\) drift (for \(r\ge8\)), and the standalone \(c=1\) exit to
\(F(r)\). The corrected root reaches
\(\mathrm{CR}(L=0^{255}1,R=[33])\) at macro 21,827 and
\(\mathrm{EL}(L=[0],R=[0,546])\) at macro 22,083. It does not reach
\(F(7)\) through the old c=2 reset.

[verify_root_corridor_macro.js](./verify_root_corridor_macro.js) is the updated
array-based regression harness for the corrected token formulas and corridor
macros. Earlier Actions runs 44978821995, 44979005652, 44979144632, and
44979251653 predate the source correction and are withdrawn for the c=2/root
chain claims. Manual V8 checks passed for the corrected token formulas at
\(n=0,\ldots,32\), c=2 values \(r=8,9,10,263\), and the 556+256-step root
continuation. The updated checked-in harness has not yet been executed under
Node/CI after editing.


## Standalone infinite projected orbit

[HPhaseGrowth.md](HPhaseGrowth.md) records a 157-step entry from the standalone
state \(H(7)\) into a tail-parametric 76-step growth loop. The 76-step identity
implies an infinite orbit of the projected outer-stack system once formalized,
but the corrected blank-root trajectory does not reach \(H(7)\) through the
previously claimed corridor.

Agent 32 matched the 76-step growth loop to 254 raw TM steps using the external
mode-closure execute blocks. The proposed direct Lean target in the mirrored
#490 module is
`evalStackCfg .CR_n_n [(1,0),(0,0)] (P ++ B ++ T) -> execute 254 -> evalStackCfg .CR_n_n [(1,0),(0,0)] (P ++ B ++ B ++ T)`.
This is a proof route for a standalone projected orbit, not a blank-root
nonhalting theorem.


## Root-reachable countdown and growth candidate

[RootCountdownGrowth.md](RootCountdownGrowth.md) records a stronger
computational route from the corrected blank root. The root reaches
\\(D_0(540)\\), follows the candidate triangular countdown
\\(S^{8n+24}(D_n(c))=D_{n+1}(c-3)\\), resets from \\(D_{180}(0)\\) to
\\(D_0(1453)\\), and reaches a new 76-step growth family at macro 1,153,484.

With
\\[
G=[0,0,1,0,1,0,0,0,0,1],\\qquad
B=[16,0,0,0,2,0,0,0,2,0,0,0],
\\]
the tested tail-parametric identity is
\\[
S^{76}(DR(G,[1]++B++T))=DR(G,[1]++B++B++T).
\\]
It preserves the left list, inserts a 12-entry block, and uses no token
normalizer. This would give an infinite projected orbit once the macro and
root prefix are source-proved. The countdown, reset, 50,000-step entry, and
76-step identity currently have computational evidence only.
