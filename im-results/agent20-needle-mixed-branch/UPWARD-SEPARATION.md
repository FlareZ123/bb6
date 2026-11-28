# Universal upward-valuation isolation in the Space Needle inverse graph

**Agent 20, 28 November 2026. Status: exact paper proof.** The all-depth source-connected cross-potential theorem is authored in Lean and awaiting original-source CI. The present *uniform in both valuations* number-theoretic inequality is a self-contained mathematical proof; a Lean kernel certificate for its universal quantifier is not yet claimed.

## Main theorem

For **every** pair \(2\le v<w\) of natural valuation labels, put

\[
D_j=2^{j+1}+3,\qquad d_j=2^j(2j-3).
\]

Then

\[
\boxed{D_w\nmid 3(d_w-d_v).} \tag{1}
\]

Consequently, take a genuine Space Needle high-level shifted target \(B\) admitting a valuation-\(w\) incoming predecessor \(P_w\), and assume it also has a valuation-\(v\) incoming predecessor \(P_v\). **The valuation-\(v\) predecessor \(P_v\) cannot itself admit a valuation-\(w\) incoming predecessor when \(2\le v<w\).** This is independent of the target counter, blank-tape reachability, or any finite selection of valuation labels. It excludes every immediate *upward switch* relative to a label already present at the target. The statement makes no assertion when \(v\ge w\), nor about arbitrary non-monochromatic multi-edge histories.

The semantic consequence follows from the exact original-source inverse edge equation and the one-step mixed-potential identity, which force \(D_w\mid 3(d_w-d_v)\) whenever both \(B\) and \(P_v\) admit a \(w\)-parent. The new generic Lean [MixedPotentialGeneral.lean](MixedPotentialGeneral.lean) and original-source [NeedleMixedPotentialSource.lean](NeedleMixedPotentialSource.lean) express the all-depth source version; the prior two special immediate exclusions \((v,w)=(3,5),(5,3)\) are source-accepted in [CI 46100959980](https://github.com/FlareZ123/bb6/actions/runs/46100959980).

## Elementary proof

Suppose, towards contradiction, that \(D_w\mid3(d_w-d_v)\). Since \(D_w=2^{w+1}+3\) is coprime to 3, this implies \(D_w\mid Q\), where

\[
Q=d_w-d_v=2^w(2w-3)-2^v(2v-3)>0.
\]

Positivity follows because \(2^j\) and \(2j-3\) are both positive and strictly increasing for \(j\ge2\). Write \(Q=D_w t\) with \(t\ge1\). Both summands in \(Q\) are divisible by \(2^v\), so \(2^v\mid Q\). Since \(D_w\) is odd, \(\gcd(D_w,2^v)=1\), implying \(2^v\mid t\), and hence \(t\ge2^v\). We obtain

\[
2^v(2^{w+1}+3)\le Q<2^w(2w-3).
\]

Cancel \(2^w\) from the strict inequality to find \(2^{v+1}<2w-3\). Since both sides are integers,

\[
2^v\le w-2,\qquad w\ge 2^v+2\ge6. \tag{2}
\]

Now consider the **small positive remainder**

\[
F=2d_v+3(2w-3)
  =2^{v+1}(2v-3)+6w-9.
\]

Using \(2d_w=(D_w-3)(2w-3)\) gives the exact identity

\[
2Q=D_w(2w-3)-F,
\]

so our assumed divisibility \(D_w\mid Q\) also implies \(D_w\mid F\).

For every integer \(v\ge2\), \(2v\le2^v\) (easy induction starting at \(v=2\)). Together with (2), this bounds

\[
\begin{aligned}
0<F
&\le 2(w-2)(w-5)+6w-9\\
&=2w^2-8w+11\\
&<2w^2.
\end{aligned}
\]

For all integers \(w\ge6\), another elementary induction gives \(2^{w+1}\ge2w^2\): at \(w=6\), \(128\ge72\); doubling the induction inequality and using \(4w^2\ge2(w+1)^2\) for \(w\ge3\) establishes the successor. Therefore

\[
0<F<2w^2\le2^{w+1}<D_w.
\]

But \(D_w\mid F\), an impossibility. This proves (1) for **all** \(2\le v<w\).

## Directionality is essential and sharp

The universal theorem cannot simply omit \(v<w\). For \(v=5,w=2\),

\[
D_2=11,\ d_5=224,\ d_2=4,\quad
3(d_2-d_5)=-660,
\]

which is divisible by 11. Moreover there is a genuine **positive prepared** two-level witness, not just a congruence: shifted target \(B=171\) admits a valuation-5 predecessor \(P_5=160\) and a valuation-2 predecessor \(P_2=124\); its valuation-5 predecessor \(160\) itself admits a valuation-2 predecessor \(116\). Each edge satisfies the original high-level source equation with nonnegative \(q\) and positive odd cofactor.

The universal upward restriction strictly generalizes all finite 42-pair **upward-direction** one-step exclusions from the [42-period dossier](README.md). It does not imply that mixed labels are permanently separated: for example, an upward 3→5 return is possible after 11 consecutive valuation-3 reverse steps, and that depth is sharp for prepared targets. The opposite 5→3 return at depth18 is consistent with the universal upward bound, which restricts only depth one when \(v<w\).

## Scientific scope

This statement is genuinely about every valuation pair in the **exact high-level dynamics of the unchanged original Space Needle machine**, not a toy relaxed map. The universal arithmetic inequality above is an elementary **paper proof**. The two special original-source Lean statements have passed CI; an explicit fully quantified Lean proof of (1) and its source corollary is a separate formalization obligation. Neither prepared reverse branching nor this necessary transition rule establishes a blank-start halting decision, so no conclusion about the exact BB(6) value is asserted.

The practical use is an **unbounded-label pruning rule** for the exact source inverse grammar: whenever a target with a known incoming \(w\)-edge is being expanded backwards along a smaller \(v\)-edge, immediately discard any attempt to follow that \(v\)-edge by \(w\) for *every* \(v<w\), without a bounded lookup table or a finite modular search.


## Strengthening to **all** original valuations, including 0 and 1

The restriction actually holds for **every pair of natural valuations \(0\le v<w\)**, once the affine correction is interpreted correctly in the integers:

\[
d_j=2^j(2j-3)\in\mathbb Z,\qquad D_j=2^{j+1}+3.
\]

The case \(v\ge2\) is the preceding proof. For the two missing cases \(v=0,1\), the correction is \(d_0=-3\) or \(d_1=-2\), respectively. The exact original high-level edge equation \(L_vB=D_vP+d_v\) still holds for these small valuations in integer arithmetic (they cannot be expressed by the earlier natural subtraction \(2v-3\), which would incorrectly truncate).

For any \(w\ge1\), \(\gcd(D_w,3)=1\). If \(D_w\mid3(d_w-d_v)\), then \(D_w\mid d_w-d_v\). Since \(2d_w=(D_w-3)(2w-3)\) (an equality of integers), we obtain

\[
D_w\mid F_{v,w}:=2d_v+3(2w-3).
\]

For \(v=0\), \(F_{0,w}=6w-15\); for \(v=1\), \(F_{1,w}=6w-13\). For **all \(w\ge3\)**, both quantities are positive and strictly less than \(D_w\). The inequality is elementary: already \(D_3=19\), while \(F_{0,3}=3\) and \(F_{1,3}=5\); incrementing \(w\) increases either \(F\) by 6 but increases \(D_w\) by \(2^{w+1}\ge16\). The only remaining small pairs \(v<w\) are \(v=0,w=1\), \(v=0,w=2\), and \(v=1,w=2\). Their respective \(3(d_w-d_v)\) are \(3,21,18\), nonzero modulo \(D_w=7,11,11\). Therefore

\[
\boxed{\forall v,w\in\mathbb N,\ v<w
\ \Longrightarrow\
D_w\nmid 3(d_w-d_v),\qquad
d_j=2^j(2j-3)\in\mathbb Z.}
\]

The original Space Needle map's valuation-\(0\) and valuation-\(1\) branches are covered by this signed equation, so the **semantic immediate-upward-switch prohibition holds for all genuine incoming valuation labels**. No \(\ge2\) exception remains in the mathematical result. The authored \`NoUpward.lean\` and source adapter currently address only \(v\ge2\); source-Lean formalization of the \(v=0,1\) signed extension is a separate outstanding step. This stronger original-machine paper theorem is still insufficient to decide the authentic blank orbit, and it does not prohibit downward switches or delayed upward returns.
