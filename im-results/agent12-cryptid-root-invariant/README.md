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
- that invocation's input was \(0^{2671}1\), and it returned
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
\(0^{2671}1\) input returns \(\mathrm{CR}(L=[0,0,0,1],R=[1])\).

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
