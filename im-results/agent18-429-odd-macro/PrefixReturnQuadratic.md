# Quadratic prefix-return separation in the #429 signed q0 macro graph

**Mathematical corollary (paper-level synthesis) of Agent 1's already Lean-checked [Q0CommonBlock](../agent1-429-q0-23-7/Q0CommonBlock.md).** The deduction below, including the asymptotic constant, has not been separately Lean-compiled. It concerns **all strict interior signed macro paths**, not just actual blank-root ancestry; it does not decide #429 or BB(6).

## Quantitative theorem

A valid macro path has rank increments in {3,4,5,6}, and digit alphabet {0,1,4,5}. Let an infinite strict path begin at rank \(p_0>0\). Write \(R(N)\) for the least positive separation \(\Delta\), if any, at which the initial N-symbol word repeats verbatim: \(d_i=d_{\Delta+i}\) for \(0\le i<N\).

**Theorem:** For any sequence \(N_j\to\infty\) such that \(R(N_j)\) is finite,
\[
\boxed{\liminf_{j\to\infty}\frac{R(N_j)}{N_j^2}\ \ge\ \frac{2}{225}.}
\]
If the recurrence gap is infinite for a given N, that N is irrelevant to the inequality. In particular, an infinite strict path **cannot** have a linearly recurrent prefix, such as one with \(R(N)\le C N\) for every N and fixed C. This excludes any candidate itinerary satisfying that regularity condition, even if nonperiodic.

### Proof via the all-depth packing theorem

Suppose an N-letter prefix repeats at gap \(\Delta>0\). The corresponding two paths share N consecutive digits and begin at ranks differing by \(L=p_\Delta-p_0\), with \(1\le L\le6\Delta\). Their common upper terminal rank is at most
\[
P=p_0+6(N+\Delta).
\]
Choose integer t with \(P<16^t\), e.g. the least such t. Agent 1's Lean-checked all-depth matching-block theorem gives for every nonnegative integer h
\[
N<\max\{t+h+B,\ 2t+3B\},\qquad
B=4^h\left(\left\lfloor\frac{L}{3\cdot16^h}\right\rfloor+1\right).
\]
Set \(x=\sqrt{L/3}\ge1/\sqrt3>1/2\). Since successive powers of four differ by a factor of four, choose h>=0 with \(x/2<4^h\le2x\). Then
\[
B\le4^h+\frac{x^2}{4^h}\le\frac52x
  \le\frac52\sqrt{2\Delta}.
\]
(The final bound uses L<=6Δ.) Thus
\[
N<2t+h+\frac{15}{2}\sqrt{2\Delta}.
\tag{*}
\]

If \(\Delta>N^2\), the desired quadratic separation is immediate. Otherwise \(\Delta\le N^2\), so \(P\le p_0+6(N+N^2)\), \(t=O(\log N)\), and the chosen \(h=O(\log N)\), all uniformly in this case. Divide (*) by N and take a subsequential lower limit of \(\Delta/N^2\):
\[
1\le\frac{15}{2}\sqrt{2\liminf \Delta/N^2},
\]
which rearranges to \(\liminf\Delta/N^2\ge2/225\). This applies to every unbounded sequence of finite prefix-return lengths N. QED.

## Research implication

The earlier eventual-periodicity prohibition is strengthened: **even arbitrarily large near-prefix recurrences must be quadratically delayed**. Primitive substitutions and other uniformly linearly recurrent symbolic constructions are therefore not candidates for an infinite strict signed q0 itinerary. To turn this into a **machine decision**, one would need a *source-root-specific upper bound* on the return gaps of any hypothetical unbounded ancestor word, or an analogous structure theorem that forces too much symbolic recurrence. No such upper bound is claimed here; arbitrary aperiodic languages can have extremely sparse prefix returns.

**Traceable basis:** [Q0CommonBlock.md](../agent1-429-q0-23-7/Q0CommonBlock.md) describes the matching-block bound, its exact all-depth lattice-packing mechanism and Lean kernel status. The additional calculus inequality and asymptotic consequence are direct paper deductions, not a second proof of the source predecessor classification.