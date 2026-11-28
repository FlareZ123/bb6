# All-scale linear-length strict predecessor family at coefficient two

**New symbolic construction (paper proof; local finite BigInt replay, not yet Lean accepted).** For every integer \(s\ge0\), put
\[
k=14\cdot4^s+4,\quad T=4^k,\quad r=k-s-3,\quad q=k-s-6,\quad N=3k-2s-6.
\]
At the exact coefficient-two center \(P=2T+4,\ Y=2\), the following **reverse chronological** half-step word admits \(N\) exact strict-interior predecessors:
\[
 \boxed{\,0^{k-1}\;1\;0^{\,r}\;111\;0^{\,q}\,}.
\]
Equivalently, the chronological word is \(0^q1110^r10^{k-1}\). Every vertex lies on the correct rank-parity phase lattice; at **every even (A) rank, the ordinate is even**, so it is an exact aligned signed macro path rather than merely a parity-relaxed branch. This is a synthetic signed-graph family, not a claim of ancestry from the blank #429 machine. It proves a one-sided obstruction to any proposed universal reverse barrier with length below \((3-o(1))k\) at \(a=2,b=4\); it does **not** give the wide windows of radius \(\asymp4^k/k\).

## Exact backward algebra

For a current state \((p,y)\), a zero predecessor has \(z=4y\), and a one predecessor has \(z=4y-q-c\). If \(p\) is even, the predecessor phase is odd: zero has \(q=p-1\), one has \(q=p-3,c=4\). If \(p\) is odd, the predecessor phase is even: zero has \(q=p-5\), one has \(q=p-9,c=12\). Every predecessor strictly decreases rank by an odd number, so the phase is automatically correct.

Write \(L_0(n)=3n-2[n\text{ odd}]\) for the total rank loss of \(n\) reverse zeros starting at even \(p\). Since \(k\) is even, \(m=k-1\) is odd and \(L_0(m)=3k-5\). The first two blocks are:
\[
\begin{aligned}
(P,2)&\stackrel{0^{k-1}}{\longmapsto}(2T-3k+9,\ T/2)\\
 &\stackrel{1}{\longmapsto}(2T-3k,\ 3k-12).
\end{aligned}
\]
The key exact tuning identity
\[
3k-12=42\cdot4^s
\]
allows another \(r=k-s-3\) zero predecessors to reach height
\[
42\cdot4^s\cdot4^r=42\cdot4^{k-3}=\frac{21}{32}T.
\]
The rank at this point is \(p_0=2T-3k-C_r\), where \(C_r=3r\) if \(r\) is even, and \(C_r=3r-2\) if \(r\) is odd.

Three consecutive inverse ones cancel the **entire \(T\)-term** of the height:
\[
\begin{array}{c|c|c|c|c}
r\pmod2 & \text{three one-step costs} & \text{height after first one} &
\text{height after second one} & \text{height after third one }H_s\\\hline
0 & 3,9,3 & 5T/8+3(k+r)-1 & T/2+15(k+r)-4 & 63(k+r)-5\\
1 & 9,3,9 & 5T/8+3(k+r)-5 & T/2+15(k+r)-14 & 63(k+r)-49
\end{array}
\]
Indeed \(64(21T/32)=42T=(16+4+1)2T\). Since \(k\) is even, \(r\equiv s+1\pmod2\). Thus
\[
 H_s=\begin{cases}
126k-63s-238,&s\text{ even},\\
126k-63s-194,&s\text{ odd}.
\end{cases}
\]
The final zero run of length \(q=k-s-6\) ends with height \(H_s4^q\).

The final rank is also explicit:
\[
 p_{\rm start}=2T+4-
 \begin{cases}
 9k-6s-4,&s\text{ even},\\
 9k-6s-6,&s\text{ odd}.
 \end{cases}
\]
This is even; \(H_s4^q\) is even. The chronological path from this state ends at \((2T+4,2)\) after exactly \(N\) half-steps, or \(N/2\) aligned signed macro steps. The whole path is strict.

## Exact radix-16 macro incarnation

The explicit even-height A-phase check above is sufficient to pair chronological bits into the *unchanged* signed macro model \(p'=p+\ell(d)\), \(16y'=y+d\,p+c_d\), with digits \(d\in\{0,1,4,5\}\), costs \(\ell=(3,5,4,6)\), and offsets \(c=(0,6,18,32)\). The chronological macro word of length \(N/2\) is especially sparse:

- For **even s** (q even, r odd):
  \[
  \boxed{0^{q/2}\ 5\ 1\ 0^{(r-1)/2}\ 1\ 0^{(k-2)/2}}.
  \]
- For **odd s** (q odd, r even):
  \[
  \boxed{0^{(q-1)/2}\ 4\ 5\ 0^{r/2}\ 1\ 0^{(k-2)/2}}.
  \]

Both have exactly **three nonzero macro digits**, even though their length tends to infinity. Their exact macro start state is
\[
 \left(\frac{p_{\rm start}}2,\ \frac{H_s4^q}2\right)
\]
and final state is \((T+2,1)\), with all intermediate strict-cone and exact divisibility guards satisfied. [long_past_family.cjs](long_past_family.cjs) independently replays these source-notation radix-16 transitions (including checking every integer division by 16) rather than relying only on even-A height. **This is the exact signed q0 macro semantics, not automatically the real blank-machine source orbit**: the macro start is synthetic and no authentic-root membership is established.

## Uniform strictness and lattice verification

The only scale fact needed is \(T=4^k\ge1024k\) for \(k\ge18\), true at 18 and propagated by multiplying the left side by four as k increases. Here \(k\ge18\), \(r,q\ge0\), and \(N\le3k\). Every ancestor rank obeys
\[
p\ge P-9N\ge2T-27k.
\]
For each maximal-height checkpoint in the five blocks, the heights are bounded respectively by
\[
 T/2,\quad 3k,\quad 21T/32,\quad
 5T/8+6k,\quad T/2+30k,\quad 126k,\quad
 2268\cdot4^{k-6}.
\]
The last bound uses \(H_s\le126k\le2268\cdot4^s\). Their triples are all **strictly smaller** than \(2T-27k\) using \(T\ge1024k\); for the tightest third bound \(3(21T/32)=63T/32\), the margin is \(T/32-27k\ge5k>0\). For the final bound \(3(2268\cdot4^{k-6})=(1701/1024)T\), the margin is at least \((347/1024)T-27k\ge320k>0\). Heights are positive: both one-block formulas are positive, \(H_s\ge63(k+r)-49>0\), and zero blocks simply quadruple positive heights. Within each zero block, heights increase and ranks decrease; strictness at the last element therefore implies strictness at every intermediate element. Each of the three individual ones is covered by the intermediate bounds.

Even-rank/A-height parity is checked at the center and after each reverse transition. Zeros yield multiples of 4. The first isolated one lands at even rank with height \(42\cdot4^s\), which is even. In the three-one block, if \(r\) is odd, the first and third outputs lie at even rank and their integer formulas are even because \(k+r\) is odd. If \(r\) is even, the second output is at even rank, with even height because \(k+r\) is even. The final zeros again yield multiples of 4. Therefore the exact phase lattice holds throughout.

These formulas prove the claim for every s, independently of finite experimental enumeration. What remains before labeling it a Lean theorem is a full formalization of the length-parametric trace/word and uniform inequalities against the unchanged original halfstep dependency.

## Maximality: the backward orbit stops at exactly N steps

This is more than a lower bound for the specifically chosen center height \(Y=2\): its *unique* strict-interior backward path has **exactly** \(N\) moves. From a current rank \(p\) and height \(y\), the zero inverse is possible only when \(12y<p-1\) if p is even, or \(12y<p-5\) if p is odd. The one inverse requires \(4y>p+1\) if p is even, or \(4y>p+3\) if p is odd. Hence the two strict inverse types are **disjoint at every vertex**, so any feasible predecessor is unique.

For the last constructed state, \(p_{\rm start}\) is even and \(y_{\rm start}=H_s4^q\). Substituting \(k=14\cdot4^s+4\) into the closed formula for \(H_s\) gives
\[
 1700\cdot4^s < H_s \le2030\cdot4^s,
 \qquad
 \frac{1700}{4096}T < y_{\rm start}
 \le \frac{2030}{4096}T.
\]
The lower estimate makes \(12y_{\rm start}>p_{\rm start}-1\) (as \(p_{\rm start}<2T+4\)), ruling out zero. The upper estimate gives \(4y_{\rm start}\le(2030/1024)T\), while
\[
 p_{\rm start}\ge 2T+4-9k
 \quad\text{and}\quad T\ge1024k.
\]
Thus \(4y_{\rm start}<p_{\rm start}\), ruling out one (\(z=4y-p_{\rm start}-1<0\)). Both branches are blocked after exactly N steps. The result is a **complete exact maximal inverse depth for this infinite set of specified centers**; it does not assert a maximum over *all* possible center heights at rank \(P\), and it is unrelated to whether any of these synthetic states is reached from #429's blank input.

The inequalities for the H-bounds are elementary: \(H_s=1764\cdot4^s+266-63s\) when s is even and \(1764\cdot4^s+310-63s\) when s is odd, together with \(4^s\ge s+1\). For s=0 equality holds at the upper endpoint, and for odd s the upper inequality is immediate from s≥1. The code now checks both absent terminal branches for every tested s.

## Reproduction and context

[long_past_family.cjs](long_past_family.cjs) replays the exact inverse operations using arbitrary-precision signed BigInt. It asserts every intermediate strict inequality and A-phase parity, the five symbolic checkpoint identities, the final length and the final height. Reproduce the initial scales with:

~~~sh
node im-results/agent18-429-odd-macro/long_past_family.cjs 0 4
~~~

The verified values are \((s,k,N)=(0,18,48),(1,60,172),(2,228,674),(3,900,2688),(4,3588,10750)\). The \(s=0\) path is exactly the maximum-depth witness at \(k=18,a=2,b=4\) in the [finite-scale interval audit](WideWindowReverseInterval.md). Its nonaccidental renormalization (the \(42\cdot4^s\) cancellation) explains one source of long, sparse-bit reverse histories.

This result **does not conflict** with [Q0Aperiodic](../agent1-429-q0-23-7/Q0Aperiodic.md), which excludes *infinite* ultimately periodic strict paths, or with [Q0HalfWindow](../agent1-429-q0-23-7/Q0HalfWindow.md), which requires a much longer **two-sided** window. Previous finite two-sided counterexamples at k=56 and k=89 do not automatically imply the present all-scale **one-sided** bound. No synthetic graph ancestor is asserted to be an actual blank-root #429 state. No improved BB(6) score or upper bound follows.
