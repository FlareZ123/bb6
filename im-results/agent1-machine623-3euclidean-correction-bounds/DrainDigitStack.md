# Ternary digit-stack normal form for the #623 evaluator

**Status:** exact case analysis of the unchanged source definition of \`evalA\`. The failure equivalence is already source-proved by \`evalA_none_iff_ternaryCongruence\`; the complete success normal form below is a mathematical derivation and has not yet been packaged as a new source theorem. Keep in \`im-results/\`.

## Exact evaluator normal form, including early exit

Read the ternary digits of \(k\) from least significant to most significant. Let \(r\) be the length of the initial run of digits equal to \(1\). Thus
\[
k=\tau(r)+3^r(3q+2\epsilon),\qquad
\tau(r)=\frac{3^r-1}{2},\qquad \epsilon\in\{0,1\},
\]
where \(\epsilon=0\) means that the first digit after the run is \(0\), and \(\epsilon=1\) means that it is \(2\). If \(k=0\), take \(r=0,\epsilon=0,q=0\).

For \(j\ge0\), define the exact third-counter cost of consuming \(j\) low-order \(1\)-digits:
\[
S_j(k)=\sum_{i=1}^{j}\left(2\left\lfloor\frac{k}{3^i}\right\rfloor+3\right),
\qquad S_0(k)=0.
\]

There are three cases.

1. **The run ends before the first counter is exhausted: \(r<a\).** The evaluator consumes all \(r\) digits \(1\), then processes the next digit:
   \[
   \operatorname{evalA}(a,k,m)
   =\operatorname{some}\bigl(a-r-1+2\epsilon,\ q,\ m+S_r(k)+2(1-\epsilon)\bigr).
   \]
   A terminal digit \(0\) decrements the positive remaining first counter and adds \(2\) to the third counter; a terminal digit \(2\) increments the first counter and adds nothing.

2. **The run ends exactly when the first counter reaches zero: \(r=a\).**
   - If \(\epsilon=0\), the next source clause is \(\operatorname{evalA}(0,0,\cdot)\), so the evaluator returns \(\operatorname{none}\).
   - If \(\epsilon=1\), the terminal digit \(2\) returns
     \[
     \operatorname{some}(1,q,m+S_r(k)).
     \]

3. **The run continues after the first counter reaches zero: \(r>a\).** This is the important early-exit case. After \(a\) recursive digit-\(1\) clauses, the source is at first counter zero and the next low digit is still \(1\). The zero-counter/digit-\(1\) clause returns immediately:
   \[
   \operatorname{evalA}(a,k,m)
   =\operatorname{some}\left(0,\left\lfloor\frac{k}{3^{a+1}}\right\rfloor,
                    m+S_a(k)\right).
   \]
   The evaluator does **not** continue to the first digit different from \(1\).

Consequently the exact failure criterion is
\[
\operatorname{evalA}(a,k,m)=\operatorname{none}
\quad\Longleftrightarrow\quad
r=a\ \text{and}\ \epsilon=0
\quad\Longleftrightarrow\quad
k\bmod 3^{a+1}=\tau(a).
\]
This agrees with the existing source theorem \`evalA_none_iff_ternaryCongruence\`.

### Correction to the earlier note

The previous statement that the \(\epsilon=0\) case fails whenever \(a\le r\) was false. It fails only when \(a=r\). If \(r>a\), the zero-counter/digit-\(1\) clause gives the early success above.

A smallest counterexample is
\[
\operatorname{evalA}(1,4,m)
=\operatorname{evalA}(0,1,m+5)
=\operatorname{some}(0,0,m+5),
\]
since \(4\) has low ternary digits \(11_3\). Here \(r=2>a=1\), so the evaluator exits successfully before reaching the following zero digit.

The formula above was compared with a direct transcription of the source recursion for all \(0\le a\le8\) and \(0\le k\le1000\) (9,009 cases, no discrepancies). This finite check is corroboration, not the proof; the case split follows by iterating the exact source clauses.

## Consequence for the two near-diagonal families

The complementary affine-buffer analysis identifies two useful special source branches:

1. Even gap-two: \(D(d+2,d)\), \(d\) even, has next step
   \[
   \operatorname{drainB}(0,d+2,2).
   \]
   Its first evaluator is \(\operatorname{evalA}(0,d+1,2d+9)\). It fails immediately exactly when \(d+1\equiv0\pmod3\), i.e. \(d\equiv2\pmod3\).

2. Odd offset-three: \(D(d+3,d)\), \(d\) odd, has next step
   \[
   \operatorname{drainB}(1,d+2,3).
   \]
   Its first evaluator is \(\operatorname{evalA}(1,d+1,2d+10)\). It fails immediately exactly when \(d+1\equiv1\pmod9\), i.e. \(d\equiv0\pmod9\).

If the first evaluator succeeds, the remaining drain can still fail. The full one-step failure criteria are already given by \`ExactEvenSectorSource.lean\`, \`ExactOddSectorSource.lean\`, and the exact finite failure-spectrum modules. The evaluator's first-step congruence is not a complete survival criterion for either family.

## Research value and limitation

The digit-stack description makes the initial evaluator transparent and, with the early-exit case included, gives its exact successful output as well as its failure condition. It is useful for composing the near-diagonal source branches with the full drain spectrum.

It does **not** show that the blank-root orbit reaches or avoids either family. Nor are these two families the complete set of possible terminal states from old-cone predecessors; see the corrected scope and explicit non-boundary terminal counterexample in \`ComplementBuffer.md\`.
