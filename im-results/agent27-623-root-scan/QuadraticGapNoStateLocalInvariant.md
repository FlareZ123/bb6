# No uniform quadratic ratio-four gap invariant on the affine cone

## Theorem

Write

\[
g(a,d)=
\begin{cases}
|a-4d|,&a\ge d,\\
|d-4a|,&a<d,
\end{cases}
\qquad m(a,d)=\min(a,d).
\]

For every positive integer C, there is an exact successful high-level transition
whose source and target both lie in the old affine cone (and hence in the
four-sector new affine cone), with

\[
g(a,d)^2\ge C m(a,d),
\qquad
g(a',d')^2<C m(a',d').
\]

Thus no fixed positive integer threshold C makes the quadratic gap condition
forward-invariant on either cone.

The fully quantified Lean theorem, including the original-source transition
and the old-cone-to-new-cone inclusion, is
[QuadraticGapNoStateLocalInvariant.lean](QuadraticGapNoStateLocalInvariant.lean).

## Explicit transition family

For any C>0, let

\[
t=\lfloor\sqrt C\rfloor,\qquad d=36+2t.
\]

The exact original high-level evaluator satisfies

\[
D(2,d)\longmapsto D(d,9).
\]

Both endpoints lie in the old affine cone:

- D(2,d) is in its right-even sector because d is even and 2(2)+2<=d.
- D(d,9) is in its left-odd sector because 9 is odd and 2(9)+8<d.

The old-cone inclusion in the exact four-sector new cone is proved using
Agent 49's source lemma ternaryOnes_ge.

The canonical gaps and smaller counters are

\[
\begin{array}{c|c|c}
 & \text{source }D(2,d)&\text{target }D(d,9)\\
\hline
g & d-8=2(t+14)&d-36=2t\\
m & 2&9
\end{array}
\]

Therefore

\[
\frac{g_{\rm source}^2}{m_{\rm source}}
 =2(t+14)^2>C,
\qquad
\frac{g_{\rm target}^2}{m_{\rm target}}
 =\frac{4t^2}{9}<C.
\]

The first inequality follows from C<(t+1)^2<(t+14)^2. The second follows
from t^2<=C and C>0.

For the specific threshold C=17, t=4 and d=44 give the concrete witness

\[
D(2,44)\longmapsto D(44,9),
\qquad
\frac{g_{\rm source}^2}{m_{\rm source}}=648,
\qquad
\frac{g_{\rm target}^2}{m_{\rm target}}=\frac{64}{9}<17.
\]

## Research implication

The finite root trace's observed lower bound g^2/m>=17 is not a state-local
property of the affine cone. This does **not** contradict the finite root
observation and does not show that the blank-root orbit visits either state
in the displayed family. It shows that an induction using only cone
membership and a fixed quadratic gap threshold cannot establish the
root-specific bound.

Any successful all-time argument must retain additional information about
the blank-root trajectory: for example, root-mass gaps, phase/history data,
or a stronger invariant that distinguishes reachable states from the
synthetic cone states above.

This is an intermediate structural obstruction, not a solution of #623 or
BB(6).

## Verification

The module compiled successfully against the unchanged upstream source in
[CI run 45455955146](https://github.com/FlareZ123/bb6/actions/runs/45455955146).
The exported theorem profile is [propext, Classical.choice, Quot.sound],
with no sorryAx. The overall workflow subsequently failed in the separate
Agent 49 carry audit: its attempted decide reductions for root indices 38
and 39 are unresolved and produce sorryAx. That failure is unrelated to
this theorem; the dedicated quadratic-gap compilation step succeeded.
