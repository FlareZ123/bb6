# Fixed-tail near-power crossing rigidity

**Status: mathematical paper proof, not yet Lean-checked.** This is a new structural obstruction inside the exact signed half-step model [Q0HalfStep](../agent1-429-q0-23-7/Q0HalfStep.lean), plus two exact scale-pinning corollaries for existing independently Lean-checked [crossing56](../agent1-429-q0-23-7/Q0HalfCounterexample.lean) and [crossing89](OddResetHalfCounterexample.lean). It is **not** an original blank-root #429 decision or a BB(6) upper bound.

## Theorem: fixed suffix templates are not scalable

Let \(a\ge1,b\ge0,t\ge0\) be fixed, and \(u,v\) fixed finite binary words. Hold k's parity fixed. There are only **finitely many** k for which a strict, exact half-step trajectory with crossing rank \(a4^k+b\) can use the consecutive words
\[
0^{k-|u|}u,\qquad 0^{k-|v|}v,\qquad 1^{k-t}.
\]
The initial state is unrestricted apart from the strict cone, correct phase, and the displayed crossing rank. The third word may continue arbitrarily; its indicated prefix suffices. In the exact model, phase A is even rank, phase B odd rank; bit 0 divides height y by 4, bit 1 divides deficit \(\delta=p-3y\) by 4. The respective rank increments are A0=5, A1=9, B0=1, B1=3, and bit-1 numerator offsets are A1=12, B1=4.

**Proof.** Write \(T=4^k\), \(r=|u|\), \(s=|v|\). The cost of n consecutive zeros is \(3n+\epsilon\) for \(\epsilon\in\{-2,0,2\}\) determined by phase and n parity. Consequently the initial rank is \(p_0=aT-3k+\gamma\). The initial ordinate must be \(y_0=C4^{k-r}\) with positive integer C. The strict cone \(3y_0<p_0\) bounds C independently of k. At entry into the fixed u suffix the rank is \(aT+b-L_u\) and the height is C. Exact recurrence along u gives
\[
4^rY=aD_uT+C+F_u,\quad D_u=\sum_{i=0}^{r-1}u_i4^i,
\]
with constant \(F_u\). The following \(k-s\) zeros force \(4^{k-s}\mid Y\). Thus \(4^{\min(k,k-s+r)}\mid C+F_u\). Since C ranges over finitely many integers, for all sufficiently large k we must have C=-F_u, unless the path is impossible. Then entry into v has *constant* integer height \(Q=aD_u4^{s-r}\) (if not integral, impossible) and rank \(aT+3k+\eta\).

Define \(D_v=\sum_{i=0}^{s-1}v_i4^i\). The exact finite recurrence along v gives
\[
4^s y_2=aD_vT+3D_vk+H_y,\quad p_2=aT+3k+H_p,
\]
with constants \(H_y,H_p\). In particular
\[
4^s\delta_2=a c T+3c k+H,\qquad
c=4^s-3D_v\ge1,\quad H=4^sH_p-3H_y,
\]
since \(D_v\le(4^s-1)/3\). The next \(k-t\) consecutive ones demand \(4^{k-t}\mid\delta_2\), hence
\[
4^{\min(k,k-t+s)}\mid(3ck+H).
\]
The positive linear integer \(3ck+H\) eventually lies strictly between zero and the exponential divisor. Contradiction for all large k. QED.

This rules out **fixed finite tails** scaling to infinity. It does *not* address histories whose nontrivial suffix lengths themselves increase with k; these are still compatible with the [wide-radius obligation](../agent1-429-q0-23-7/Q0HalfWindow.md).

## Quantitative, word-uniform strengthening

The argument also yields a **fully explicit obstruction covering every choice of words of the given lengths**, not just one fixed u,v. In particular there is no need to fix the parity of k.

Let \(r=|u|,s=|v|\) and \(r,s,t\le k\), with \(a\ge1,b\ge0\). Define
\[
 B=a+2b+21r+16,\qquad A=a+2b+24s+16.
\]
Then **no strict exact path of the displayed three-block form exists if all three conditions hold**:
\[
 \boxed{4^{\,k-\max(r,s)}>B,\qquad
        3k>4^s A,\qquad
        4^{\,k-\max(s,t)}>3k+A.}
\]
This is a uniform arithmetic test depending only on a,b,k and the three word lengths, not on their contents.

**Proof of explicit bounds.** The initial rank is \(p_0=a4^k-3k+\gamma\) with \(\gamma=b+3r-L_u-\epsilon\) and \(|\gamma|\le b+12r+2\). The strict cone bounds the positive integer C after the first zero run by \(C\le a4^r+b+12r+2\). The first-tail constant \(F_u\), built from the phase offsets and ranks \(b-L_u+L_i\), satisfies
\[
 |F_u|\le(b+9r+12)(4^r-1)/3.
\]
Hence \(|C+F_u|\le4^r B\). The first displayed condition implies
\[
4^{\min(k,k-s+r)}=4^{r+k-\max(r,s)}>4^r B,
\]
forcing \(C+F_u=0\) by divisibility. The resulting *integer* height Q at the start of v satisfies \(3Q<a4^s\), from \(4^rQ=aD_u4^s\) and \(3D_u<4^r\).

Now the rank at the start of v is \(a4^k+3k+\eta\), where \(|\eta|\le b+3s+2\); its final rank offset \(H_p\) obeys \(|H_p|\le b+12s+2\). The finite v recurrence gives a constant \(H_y=Q+\sum_{i<s}4^i[v_i(\eta+L_i)+\operatorname{off}_i]\), with
\[
3|H_y|<4^s(a+b+12s+14).
\]
Consequently the constant \(H=4^sH_p-3H_y\) in the deficit identity obeys \(|H|<4^s A\). Since \(1\le c=4^s-3D_v\le4^s\), the second displayed condition makes the integer \(3ck+H\) strictly positive, and
\[
0<3ck+H<4^s(3k+A).
\]
The third condition makes this smaller than the divisor \(4^{\min(k,k-t+s)}=4^{s+k-\max(s,t)}\). Contradiction. QED.

**Asymptotic consequence.** Fix a,b and any \(\varepsilon>0\). For all sufficiently large k, *uniformly over all u and v*, if \(r,t\le k/2\), then any such crossing must have
\[
s>(1-\varepsilon)\log_4 k.
\]
Indeed if \(s\le(1-\varepsilon)\log_4 k\), then \(4^s A=O(k^{1-\varepsilon}\log k)=o(k)\), while the first and third inequalities follow because their powers have exponents at least \(k/2-O(\log k)\) and the right sides are polynomial in k. More precisely, for all sufficiently large k (depending on fixed a,b), the first and third displayed inequalities hold uniformly for **all** lengths r,s,t at most k/2. Therefore every admissible crossing with r,t at most k/2 must satisfy
\[
3k\le 4^s(a+2b+24s+16)
\]
(whether s is small or large; for s>k/2 this holds automatically for sufficiently large k). Splitting into s at most \(\log_4 k\) and s greater than \(\log_4 k\) gives the sharper uniform growth bound
\[
\boxed{s\ \ge\ \log_4 k-\log_4(a+2b+24\log_4 k+16)+\log_4 3
       \ =\ \log_4 k-O(\log\log k).}
\]
This is a **quantitative minimum active suffix length** for scalable crossings with substantial outside homogeneous runs. It is still much weaker than the all-word wide-window impossibility needed for #429.

## Sharp existing coefficient-two template: k=56 only

For even \(k\ge10\), require rank \(2\cdot4^k+2\) after \(w=0^{k-9}\texttt{101100000}\), then \(v=0^{k-10}\texttt{1011111111}\) followed by \(k-10\) ones. Write \(T=4^k\). Necessarily
\[
p_0=2T-3k-6,\quad y_0=C4^{k-9},\quad 1\le C\le174762.
\]
The first tail yields \(4^9Y=162T+C-843\). The second zero prefix forces \(4^{k-1}\mid C-843\), hence C=843, and the second tail starts with height 648. Its exact endpoint is
\[
4^{10}y_2=699042T+1048563k+10486488,\quad p_2=2T+3k+30,
\]
so \(4^{10}\delta_2=26T+39(k-56)\). The third one prefix requires \(4^k\mid39(k-56)\); since \(4^k>39|k-56|\) for every k>=10, **k=56**. The earlier Lean crossing56 attains this scale.

## Sharp existing coefficient-one template: k=89 only

For odd \(k\ge9\), require rank \(4^k\) after \(w=0^{k-4}\texttt{1110}\), then \(v=0^{k-5}\texttt{11111}\) and \(k-8\) ones. Necessarily
\[
p_0=T-3k-8,\quad y_0=C4^{k-4},\quad 1\le C\le85,\quad
4^4Y=21T+C-14.
\]
The second zero prefix forces \(4^{k-1}\mid C-14\), so C=14 and v starts at height 84. Its endpoint is
\[
4^5y_2=341T+1023k+6233,\quad p_2=T+3k+18,
\]
and \(4^5\delta_2=T+3(k-89)\). The third one prefix gives \(4^{k-3}\mid3(k-89)\), and \(4^{k-3}>3|k-89|\) for k>=9. Thus **k=89**, attained by the earlier Lean crossing89.

## Reproduction and evidence limitations

[template_rigidity.cjs](template_rigidity.cjs) derives exact finite-tail symbolic coefficients in BigInt and replays all primitive half-steps of both witnesses, checking integrality, strict positivity, and rank parity. The general all-k theorem is a paper argument, **not** an automatically checked Lean theorem; the script validates algebra only. Useful next tasks: formalize the finite-template lemma directly using Q0HalfStep.Trace, and seek an all-scale obstruction on genuinely scale-dependent delayed histories. The present theorem excludes a natural spurious extrapolation of two short counterexamples, not the surviving wide-window problem.