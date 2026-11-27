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

## Stronger theorem: quadratic *factor complexity* for every infinite signed path

The same argument yields a substantially stronger conclusion that does **not require any prefix to recur**.

For an infinite strict-interior macro digit sequence \(d_0d_1\ldots\), let
\[
  P_d(N)=\#\{(d_i,\ldots,d_{i+N-1}):i\ge0\}
\]
be its standard length-N subword/factor complexity.

**Theorem.** Every such sequence satisfies
\[
\boxed{\displaystyle
\liminf_{N\longrightarrow\infty}\frac{P_d(N)}{N^2}
  \ \ge\ \frac{2}{225}.}
\]
In fact, for every \(c<2/225\) and all sufficiently large N (depending on the starting rank), **all length-N factors starting at positions \(0,1,\ldots,\lfloor cN^2\rfloor\) are pairwise distinct**.

**Proof.** Suppose two length-N factors starting at \(0\le i<j\le\lfloor cN^2\rfloor\) agree. Their rank gap is \(L=p_j-p_i\le6(j-i)\le6cN^2\); both terminal ranks are at most \(p_0+6(j+N)\le p_0+6(cN^2+N)\). Let t be the first integer such that these ranks are below \(16^t\), and choose h as above. Uniformly in the pair, \(t,h=O(\log N)\) and the same exact matching-block packing theorem implies
\[
N<2t+h+\frac{15}{2}\sqrt{2(j-i)}
 \le O(\log N)+\frac{15}{2}\sqrt{2c}\,N.
\]
Since c<2/225 makes \((15/2)\sqrt{2c}<1\), the inequality is impossible at all sufficiently large N. Hence the first \(\lfloor cN^2\rfloor+1\) length-N factors are distinct, so \(P_d(N)\ge\lfloor cN^2\rfloor+1\). Let c approach 2/225 to obtain the displayed liminf. QED.

**Consequences.** Any infinite strict signed q0 itinerary has *at least quadratic subword complexity*. This excludes not merely eventual periodicity and linearly recurrent prefixes but every proposed itinerary of subquadratic factor complexity—for example any candidate sequence with bounded factor complexity \(O(N)\), including Sturmian and primitive substitution symbolic words. The conclusion is a **paper corollary of an existing Lean-checked all-depth arithmetic packing theorem**; this new complexity theorem has not itself been compiled in Lean. Crucially, high-complexity aperiodic digit sequences remain possible, and the original #429 genuine blank-root question is still open.

## Research implication

The earlier eventual-periodicity prohibition is strengthened: **even arbitrarily large near-prefix recurrences must be quadratically delayed**. Primitive substitutions and other uniformly linearly recurrent symbolic constructions are therefore not candidates for an infinite strict signed q0 itinerary. To turn this into a **machine decision**, one would need a *source-root-specific upper bound* on the return gaps of any hypothetical unbounded ancestor word, or an analogous structure theorem that forces too much symbolic recurrence. No such upper bound is claimed here; arbitrary aperiodic languages can have extremely sparse prefix returns.

**Traceable basis:** [Q0CommonBlock.md](../agent1-429-q0-23-7/Q0CommonBlock.md) describes the matching-block bound, its exact all-depth lattice-packing mechanism and Lean kernel status. The additional calculus inequality and asymptotic consequence are direct paper deductions, not a second proof of the source predecessor classification.