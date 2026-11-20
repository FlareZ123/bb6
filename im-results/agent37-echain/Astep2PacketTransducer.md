# Canonical packet transducer for the external 107-call A-step chain

## Scope

This is an intermediate symbolic reconstruction of the external halting-cylinder proof after its first DRegular exit. It is based on the primitive replay in [Astep2BoundaryReplay.mjs](Astep2BoundaryReplay.mjs), which checks every macro tail and the eleven Lean checkpoints. It is not a proof that the authentic blank-tape orbit enters this cylinder and is not a BB(6) result.

## Canonical packet representation

Write
\[
P(q,p;Y)=(01)^q\,0\,1^p\,Y,
\]
with the canonical convention that \(Y\) is empty or begins with \(0\). Any leading ones of a proposed tail are absorbed into \(p\). This resolves the non-uniqueness in the earlier packet trace: for example, call 24 is canonically \(P(0,9;010111)\), not \(P(0,8;1010111)\).

After call 11 the state is \(P(0,8;0111111)\). Every later suffix through call 107 has a canonical packet decomposition, and the following two ordinary rules account for all non-boundary calls:

- **B packet edge**, \(q>0\):
  \[
  (a,q,p,Y)\mapsto
  \left(8\frac{a-2}{3}+10,\ q-1,\ p,\ Y\right).
  \]
- **E packet edge**, \(p\ge3\):
  \[
  (a,q,p,Y)\mapsto
  \left(8\frac{a-4}{3}+9,\ q+2,\ p-3,\ Y\right).
  \]

These are precisely the `PacketRank.advance` updates and preserve the tail \(Y\).

## E-zero boundary: a simple general rule

Seven observed E-zero boundaries satisfy the same exact formula:

\[
P(q,0;01Y)\longmapsto P(0,2q+7;Y),\qquad q>0.
\]

The unary parameter update is \(a'=8(a-4)/3+5\). The calls are:

| Call | Input | Output |
|---:|---|---|
| 24 | \(P(1,0;01010111)\) | \(P(0,9;010111)\) |
| 32 | \(P(2,0;010111)\) | \(P(0,11;0111)\) |
| 47 | \(P(2,0;0101)\) | \(P(0,11;01)\) |
| 67 | \(P(1,0;0101011111)\) | \(P(0,9;01011111)\) |
| 75 | \(P(2,0;01011111)\) | \(P(0,11;011111)\) |
| 91 | \(P(1,0;0101011)\) | \(P(0,9;01011)\) |
| 99 | \(P(2,0;01011)\) | \(P(0,11;011)\) |

This is a strong candidate for a general Lean source lemma. It is more informative than treating these seven endpoints as unrelated suffix facts.

## E-two boundary cases

Five E-two boundaries occur in this chain. The replay checks their exact input/output packet states and the same unary update \(a'=8(a-4)/3+5\):

| Call | Input | Output |
|---:|---|---|
| 18 | \(P(0,2;0111111)\) | \(P(0,6;01010111)\) |
| 42 | \(P(0,2;0111)\) | \(P(0,6;0101)\) |
| 54 | \(P(3,2;01)\) | \(P(0,8;011111111)\) |
| 61 | \(P(0,2;011111111)\) | \(P(0,6;0101011111)\) |
| 85 | \(P(0,2;011111)\) | \(P(0,6;0101011)\) |

The E-two reset is therefore not one fixed-tail case: it includes a \(q=3\), short-tail branch at call 54. A general theorem should retain both \(q\) and \(Y\), rather than hard-code only the \(P(0,2;0111111)\) instance.

## Complete packet lifecycle

The 96 calls after call 11 are parsed by:
1. B edges for \(q>0\);
2. E edges for \(p\ge3\);
3. the E-zero rule above;
4. the five observed E-two reset cases above.

The final state after call 107 is
\[
P(1,2;011),
\]
with suffix `01011011` and final unary parameter
`7488166283129708930486796847462680979065226437987146331898837006603604720521272903526417758309106`. At this point the external Lean proof applies `step_An_1101` and then `iterate 113 stepHalt`; the packet trace ends at the input to that terminal source lemma, not at the halting configuration itself.

The updated replay script asserts the canonical packet state at every call, all ordinary unary recurrences, every E-zero formula instance, all five E-two reset instances, and the final packet state. The same state loop was run in the JS tool runtime and all 107 calls passed.

## Research consequence

The 107-call external chain can be reduced to a small packet transducer plus a finite set of exceptional E-two source cases. The highest-value formalization targets are:
- a general E-zero source lemma \(P(q,0;01Y)\to P(0,2q+7;Y)\);
- an E-two source lemma parameterized by \((q,Y)\), covering the five observed reset shapes;
- a compact theorem that composes these packet transitions to the terminal halting configuration.

This remains an external-cylinder analysis. The missing blank-tape prefix/root-reachability bridge remains the decisive obstacle to BB(6).
