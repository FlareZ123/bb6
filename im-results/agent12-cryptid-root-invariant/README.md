# Corrected blank-root stack trajectory: accelerated experiment

**Status:** computational evidence and a candidate invariant, not a proof of nonhalting.

## Experiment

The corrected root seed is the #85-oriented stack configuration

\[
\mathrm{DR}(L=[0,0],R=[1]),
\]

entered at raw TM time 7. The fast interpreter in
[\`fast_root_stack_sim.js\`](./fast_root_stack_sim.js) is a persistent-linked-list
transcription of the four outer mode rules and token normalizers in
[\`../agent32-cryptid-padding/stack_system_sim.py\`](../agent32-cryptid-padding/stack_system_sim.py).
Unlike the array-based exploratory implementation, it retains shared list tails
and can run a million macro-successor steps without copying the entire right
stack at each transition.

A run of 1,000,000 macro-successor steps produced:

- no \`TokenHalt\` branch;
- no \`mode_CR\` left-head-\(\ge2\) branch;
- no \`closeTokCR\` invocation;
- exactly one \`closeTokDR\` invocation, at macro index 21,810;
- that invocation's input was \(0^{267}1\), and it returned
  \(\mathrm{CR}(L=[0,0,0,1],R=[1])\);
- 268 \`bounceDR\` calls and zero \`bounceCR\` calls;
- maximum left-list length 268, maximum right-list length 154,446,
  maximum entry 203, and maximum number of ones in the left list 10.

At macro index 1,000,000 the state was

\[
\mathrm{CR}\left(
L=[0,0,1,0,0,0,0,1],\
R=[0,0,0,0,16,0,0,0,2,0,0,0,2,0,0,\ldots]
\right),
\]

with right-list length 154,441.

These are macro-successor counts, **not raw TM steps**. The accelerated run is
a computation over the source-derived stack successor, not a formal proof that
the TM runs forever. The Python implementation was not executed in this
invocation; the JavaScript implementation was executed in the available V8
runtime. The first root prefix was independently matched against the raw
transition table.

## Candidate inductive invariant

The experiment checked the following predicate before every one of the
1,000,000 successor applications, without finding a counterexample. It is a
candidate for formalization, not yet an established invariant.

Write \(Z_1=0^*(\epsilon\mid1)\), and let \(\operatorname{firstNZ}(R)\)
be the first nonzero entry of \(R\), if any.

1. Every entry of \(L\) belongs to \(\{0,1\}\).
2. In mode DR, \(R\) is nonempty and its head is positive.
3. In mode EL:
   - if the head of \(R\) is 1, \(L\) begins with 0;
   - if \(\operatorname{firstNZ}(R)=2\), then \(L\in Z_1\);
   - if the head of \(R\) is 1 and the first nonzero entry of the tail of \(R\) is 2, then \(L\in\{\epsilon,[0]\}\).
4. In mode DL:
   - if the head of \(R\) is 0, \(L\) begins with 0;
   - if the head of \(R\) is 1, then \(L\in Z_1\);
   - if the head of \(R\) is 0 and the first nonzero entry of the tail of \(R\) is 2, then \(L\in\{\epsilon,[0]\}\).
5. In mode CR, if \(L\) begins with \([1,1]\) and the head of \(R\) is 1, then \(L\) with its first two entries removed belongs to \(Z_1\).

The exact predicate, including the finite lookahead conditions, is implemented
by \`invariantFailures\` in the JavaScript interpreter.

## Why this could matter

If the predicate is proved inductive for the exact successor relation, it
excludes the two halting mechanisms in the stack reduction:

- the direct CR branch with left head at least 2, by item 1;
- the CR token-halting branch, provided the only token entry is a DR-token
  closure from a DL state with right head 1 and left list in \(Z_1\), while
  DR states never have right head 0.

For \(L\in Z_1\), the DR token normalizer is elementary: it consumes the
leading zeros, optionally consumes one terminal 1, and returns a CR stack
state with binary left list. In particular, the observed
\(0^{267}1\) input returns \(\mathrm{CR}(L=[0,0,0,1],R=[1])\).

The main unresolved task is to prove the candidate predicate is preserved by
every successor case, including the interaction between leading-zero prefixes
of \(R\) and the regular-language conditions on \(L\). A finite trace is not
evidence of inductiveness. If the proof succeeds, it would give a route to a
formal nonhalting result for this blank-root machine; if it fails, the first
symbolic counterexample should refine the invariant rather than be patched
with more finite simulation.


## Counterexample-guided audit of the candidate

A small exhaustive one-step search over short lists found that the predicate
above is **not inductive over all configurations satisfying it**. These
counterexamples are not known to be reachable from the blank root; they show
that the observed-trace predicate is too weak to serve directly as a global
invariant.

Examples (input state \(\to\) successor):

- \(\mathrm{CR}(L=[1,1],R=[2])\to
  \mathrm{EL}(L=[0,0,0,0],R=[1,0,2])\).
  The successor violates the EL condition for a leading nonzero pattern
  \(1,2\).
- \(\mathrm{CR}(L=[0,1,1],R=[])\to
  \mathrm{CR}(L=[1,1],R=[2])\).
  The successor violates the CR condition on a left prefix \(1,1\).
- \(\mathrm{CR}(L=[1,0,1],R=[1])\to
  \mathrm{CR}(L=[1,1],R=[0,0,2])\).
- \(\mathrm{EL}(L=[0],R=[1,1,2])\to
  \mathrm{DL}(L=[0],R=[0,1,2])\).
- \(\mathrm{EL}(L=[],R=[0,0,1,2])\to
  \mathrm{EL}(L=[0],R=[0,1,2])\).

The counterexamples expose a recurring dependency on the nonzero subsequence
of \(R\): prefixes of the form \(1^k2\), together with the number of leading
zeros, determine whether later EL/DL transitions produce a token-dangerous
configuration. A stronger invariant will likely need a finite-state relation
between the regular shape of \(L\) and an automaton state summarizing the
nonzero prefix of \(R\), rather than the current small collection of
independent implications.

The million-step root trace still satisfies the predicate actually checked by
the script. That is a statement about this finite trace only. Do not promote
the current predicate to a proof or use it to claim nonhalting.


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

The source-derived bounce rules give a simple exact formula for the only
token closure observed on the root trace. For any right context \(r\):

\[
\begin{aligned}
\operatorname{closeTokDR}(r,0^n)
  &= \mathrm{CR}(L=[0,1],\,R=\operatorname{bump}(r)),\\
\operatorname{closeTokDR}(r,0^n1)
  &= \mathrm{CR}(L=[0,0,0,1],\,R=\operatorname{bump}(r)).
\end{aligned}
\]

Indeed, bounceDR with initial accumulator \([0]\) maps \(0^n\) to
\(([1^n,0],[1])\), and maps \(0^n1\) to
\(([1^{n+1},0],[0,0,1])\). The EL normalizer erases the leading ones in the
accumulator; its final zero emits the displayed CR configuration. Thus every
input in \(Z_1\) is token-safe for this DR closure. The macro-21,810 event is
the second case with \(n=267\) and empty context \(r\).

## Exact corridor macro family

`RootCorridorMacro.md` gives four exact macro identities for the family `Corr(r,c)=DR(L=0^r1,R=[1,c])`: the `c≥3` decrement-by-three step, the `c=0` reset, the `c=2` token-normalizer reset, and the `c=1` exit to `F(r)`. Composed with the observed root entry at macro 24, these identities explain the corridor-family prefix through `F(7)` at macro 21,888. They are exact transition derivations, but they do not yet close the subsequent orbit or prove nonhalting.

`verify_root_corridor_macro.js` is a self-contained array-based regression harness for the four identities, the arbitrary-tail DR transfer, the empty-context `0^n1` token closure, and selected root-chain transitions. The harness is self-contained and runs under Node 20: `node im-results/agent12-cryptid-root-invariant/verify_root_corridor_macro.js`. A temporary one-off workflow was used for regression validation and removed after the passing run; no dedicated workflow is retained. The harness is computational support, not a formal proof.

Regression status: `verify_root_corridor_macro.js` passed Actions run `44978821995` (commit `983702c7e6e15d3edb96cfb60565d82b79c973d6`) with 89 checks. This does not replace a formal proof.


The macro regression harness also verifies `F(r) -> G(r)` in `3r+13` successors, where `G(r)=DR(0^2(10)^(r+2)0^2 1 0^3,[1,0])`. The root prefix therefore reaches `G(7)` at macro 21,922. Latest CI pass: Actions run `44979005652`, 97 checks.


The root macro prefix now includes `G(7)` at 21,922 and `H(7)` at 21,926, with the four-step `G(r) -> H(r)` identity checked for r=1..8. Latest regression pass: Actions run `44979144632`, 105 checks. The H-family orbit is open.


The regression harness also checks the 24-step prefix from the accelerated root stack seed `DR([0,0],[1])` (raw TM time 7) to `Corr(3,3)`. Latest CI run `44979251653` passed 106 checks, covering the executable root prefix through `H(7)` at macro 21,926. This remains computational support, not formal proof.


The recorded 106-check run predates the notation-only `E` -> `Corr` rename and seed-time label clarification; the transition logic was unchanged, but no post-edit run is claimed.
