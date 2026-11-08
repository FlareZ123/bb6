# Exact local inverse-degree law and limiting distribution for Machine C

**Claim.** The original Machine C first-return section has a closed-form, all-target inverse degree for every output \((x,y)\) with \(x\ge0,\ y\ge5\). Outside two thin dyadic diagonals, the degree depends only on the 2-adic valuation of \(x+y\) or \(x+y+1\) and the parity of \(y\). In expanding rectangular windows its predecessor-count distribution has a geometric tail. This is a structural theorem about the **full, unmodified source section**, not about which states are reached from the blank tape; Machine C and BB(6) remain unresolved.

**Proof status.** The argument below is a complete mathematical derivation from the original-source Lean theorem [\`BB6.Agent46.section_preimage_all_iff\`](../im-results/agent3-c-bounce-inverse/SectionAllInverse.lean), whose unchanged-source proof passed [CI 41544188316](https://github.com/FlareZ123/bb6/actions/runs/41544188316). The derived degree and asymptotic distribution are **paper proofs, not separately kernel-checked Lean theorems**. The previous [all-target, kernel-certified upper bound](../im-results/agent34-c-valuation-fanin/ValuationDegreeBound.lean) was \(d(x,y)\le \lfloor V/2\rfloor+1\) and did not give the exact distribution. An independently written source-shaped oracle validates the formula on 97,300 targets; finite tests are supplementary, not the proof.

## Exact law

Let \(d(x,y)=|\{(a,k)\in\mathbb N^2:\operatorname{secNext}(a,k)=\operatorname{some}(x,y)\}|\). Given \(y\ge5\), set
\[
S=x+y,\quad Q=\begin{cases}S&S\text{ even},\\S+1&S\text{ odd},\end{cases}
\quad V=\nu_2(Q),\qquad P=[Q=2^V],
\]
where \([A]\in\{0,1\}\) is the indicator of statement \(A\). Necessarily \(V\ge1\). Define
\[
B(V,y)=\left\lfloor\frac V2\right\rfloor+
[V\text{ odd and }y\text{ even}].
\]
**Theorem 1 (exact all-target degree).**
\[
\boxed{d(x,y)=
\begin{cases}
B(V,y), & P=0,\\
B(V,y)+1,&P=1,\ S\text{ even},\ x\equiv V\pmod2,\\
B(V,y)-1,&P=1,\ S\text{ even},\ x\not\equiv V\pmod2,\\
B(V,y)-1,&P=1,\ S\text{ odd},\ x\equiv V\pmod2,\\
B(V,y),&P=1,\ S\text{ odd},\ x\not\equiv V\pmod2.
\end{cases}}
\]
The formula includes every finite source pair and all exceptional input branches. The only nonzero corrections to the generic law lie on \(x+y=2^v\) or \(x+y=2^v-1\).

### Proof of Theorem 1

Invoke the exhaustive \`section_preimage_all_iff\`. For \(y\ge5\), every parent has exactly one of the following *disjoint* input forms: a direct parent with \(a\ge2,\ 0<k,\ 2k\le a\); an ordinary high-bounce parent \(a\ge2,\ 2k>a\); an exceptional \(a=0,k\ge2\) or \(a=1,k\ge4\); or one of the special \((1,2),(1,3)\).

A direct parent occurs **if and only if \(y\) is even**: it is uniquely \((a,k)=(S-2,(y-2)/2)\). Since \(y\ge6\) in this case, all input guards hold.

**Even \(S\).** Write \(S=2^Vu\) with \(u\) odd. Every ordinary high parent has even \(a\ge2\) and a unique depth \(n\) satisfying the source-certified equations
\[
S=2^{n+1}(a+2),\qquad 2k+a+7+3n=S+y.
\]
Thus \(a=2^{V-n-1}u-2\), and parity of the second equation gives \(n+1\equiv x\pmod2\). If \(u\ge3\), every \(0\le n\le V-2\) of that parity yields a parent. If \(u=1\), the final depth \(n=V-2\) is lost because it gives \(a=0\); all earlier permitted depths work. No higher depth gives an even \(a\ge2\).

For sufficiency, the displayed equations give integer \(k\). Their high-branch guard is automatic:
\[
2k-a=(2^n-1)(2a+4)+y-3-3n>0,
\]
using \(2^n-1\ge n\), \(a\ge2\), \(y\ge5\). Thus \(k>0\) and \(2k>a\), and the **converse** direction of the certified source iff produces a real section edge.

An \(a=0\) parent is possible exactly for \(u=1,\ V\ge3,\ x\equiv V\pmod2\). It is unique, with \(k=(2^V+y-3V)/2\ge2\). Hence, relative to the \(u\ge3\) depth count, pure powers lose one high parent precisely when \(x\not\equiv V\pmod2\), and gain one exceptional parent precisely when \(x\equiv V\pmod2\). The direct contribution completes the first three branches of the formula.

**Odd \(S\).** Now write \(Q=S+1=2^Vu\) with \(u\) odd. Every ordinary high parent has odd \(a\ge3\) and the exact source equations
\[
Q=2^{n+1}(a+3),\qquad 2k+a+7+3n=S+y.
\]
Consequently \(a=2^{V-n-1}u-3\) and \(n\equiv x\pmod2\). For \(u\ge3\) every permitted \(0\le n\le V-2\) gives a parent. When \(u=1\) both final depths \(V-3,V-2\) are lost, leaving \(0\le n\le V-4\). The high-branch guard follows from
\[
2k-a=(2^n-1)(2a+6)+y-2-3n>0.
\]
For \(u=1,\ V\ge4\), the unique exceptional \(a=1,k\ge4\) parent exists precisely when \(x\not\equiv V\pmod2\), with \(k=(2^V+y-3V)/2\). For \(V=3\), the two high depths are absent and there is instead one special parent \((1,2)\) when \((x,y)=(2,5)\) or \((1,3)\) when \((x,y)=(0,7)\). These are exactly the possible \(x\) even, \(y\ge5\), \(S=7\) targets. Thus **for every pure-power odd \(S\)** one of the two lost high-depth slots is restored exactly when \(x\not\equiv V\pmod2\), yielding the last two branches.

Finally, for nonpure \(Q\) both parity depth counts \(0\le n\le V-2\), together with the direct contribution \([y\text{ even}]\), simplify to \(B(V,y)\). Distinct depths give distinct \(a\); direct, high and exceptional input ranges do not overlap, so no parent is double-counted. This proves the theorem.

## Exact limiting degree distribution

Let
\[
T_N=\{(x,y):0\le x<N,\ 5\le y<N\}\qquad(N>5).
\]
**Theorem 2 (asymptotic distribution).** The fraction of targets in \(T_N\) with exactly \(r\) immediate section parents converges to
\[
\boxed{\lim_{N\to\infty}\frac{\#\{(x,y)\in T_N:d(x,y)=r\}}{|T_N|}
=\begin{cases}\frac14,&r=0,\\[2mm]\frac{9}{4^{r+1}},&r\ge1.\end{cases}}
\]
In the same limit the mean inverse degree is **1**, the second moment is **\(5/3\)**, and the variance is **\(2/3\)**. The image of the successful source-return map occupies limiting density **\(3/4\)** in these windows.

**Proof.** Each of the two exceptional sums \(S=2^v,2^v-1\) contributes at most \(N\) points to the window; only \(O(\log N)\) exponents occur, hence the exceptional locus has \(O(N\log N)\) points, of density zero. For any fixed \(v\ge1\), \(\nu_2(Q)=v\) means \(S\equiv2^v\) or \(2^v-1\pmod{2^{v+1}}\), which has limiting density \(2^{-v}\). Within these residue classes exactly half of the targets have even \(y\). Off the exceptional locus, Theorem 1 gives
\[
d=\begin{cases}v/2,&v\text{ even},\\
(v+1)/2,&v\text{ odd and }y\text{ even},\\
(v-1)/2,&v\text{ odd and }y\text{ odd}.
\end{cases}
\]
Thus \(p_0=2^{-1}/2=1/4\) and, for \(r\ge1\),
\[
p_r=2^{-2r}+\tfrac12\,2^{-(2r-1)}
+\tfrac12\,2^{-(2r+1)}=9/4^{r+1}.
\]
Finite-modulus residue counting proves each fixed \(r\) limit. The fraction of targets with valuation \(V\ge L\) is at most \(O(2^{-L})+O(1/N)\), so no probability mass escapes. Moreover \(d\le V/2+1\) by the existing source-certified bound, and \(V=O(\log N)\) within \(T_N\); this controls the tails and permits termwise limiting of the first two moments. Evaluate the geometric sums \(\sum_{r\ge1}r p_r=1\), \(\sum_{r\ge1}r^2p_r=5/3\). Finally \(d=0\) exactly when a target has no section predecessor, so image density equals \(1-p_0=3/4\).

## Implications and reproducibility

The distribution proves that although inverse fans can be arbitrarily large along dyadic diagonals, degree \(0\) and \(1\) dominate typical targets; the exact finite exceptions are completely explicit. This supplies a closed-form weight for backward-search scheduling and confirms that high-deg valuations concentrate on a zero-density set. It does **not** estimate the probability of halting or restrict the authentic blank-root orbit by itself.

- Established source semantics: [SectionAllInverse.lean](../im-results/agent3-c-bounce-inverse/SectionAllInverse.lean) and [successful unchanged-source CI 41544188316](https://github.com/FlareZ123/bb6/actions/runs/41544188316).
- Prior source-checked bound: [ValuationDegreeBound.lean](../im-results/agent34-c-valuation-fanin/ValuationDegreeBound.lean), [CI 42249415695](https://github.com/FlareZ123/bb6/actions/runs/42249415695).
- Independent arithmetic and forward-source regression: [check_degree.py](../im-results/agent34-c-degree-profile/check_degree.py), deterministic seed 746623, 97,300 targets.
- **Open:** produce a separate kernel proof of the closed-form count if valuable, and use the exact degree in a genuinely blank-root-sensitive inverse closure. Neither of the theorems above determines any unresolved machine's halt status.
