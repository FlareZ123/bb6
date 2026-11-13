# Bounded finite-word converse: shadow paths lift to original P1 inverse cones

**Status (2026-11-13):** Agent 50 independently reviewed the core source-size and exceptional-counter argument under the earlier, stronger $N\ge2M+16$ margin. The Lean candidate now accepts the more general direct width hypothesis $L+M\le2^{N-M-3}$. For the feeder range $N+8\le L\le N+9$, the simple sufficient condition $N\ge2M+7$ implies this width bound; that sharpening and the direct-width formalization still await independent review and Lean CI. This is an intermediate result in `im-results/`, not a publishable theorem yet.

## Statement

Let $N=16q$, let $L=N+h$ with $h\in\{8,9\}$, and use the corresponding feeder root:
- $L=N+8$, $z_0=12q+4$, $(b_0,d_0)=(4u-4,4u+9)$, $\alpha_0=28$;
- $L=N+9$, $z_0=10q+4$, $(b_0,d_0)=(6u-2,2u+5)$, $\alpha_0=42$,

where $u+4q+3=7\cdot2^N$.

The proposed general theorem is:

> For every abstract feeder-rooted `ShadowReach` path ending at cost $m\le M$, if
> $N+8\le L,\qquad L+M\le2^{N-M-3},$
> then that path has a realization by the original source `OddCone` and the unchanged `inverseAt` definition.

For the two feeders, $L\in\{N+8,N+9\}$. A simple uniform sufficient condition is $N\ge2M+7$: with $K=N-M-3$, this gives $K\ge M+4\ge4$ and
> $L+M\le N+M+9=K+2M+12\le3K+4\le2^K.$
> The feeder corollaries therefore apply whenever $q\ge\lceil (2M+7)/16\rceil$. The direct width hypothesis is stronger and allows larger finite windows at fixed $q$. This is a finite-word converse, not a bound uniform over unbounded $M$ at fixed $q$.

The formal candidate is [ShadowGraphConverse.lean](./ShadowGraphConverse.lean), with exact-width feeder corollaries `l0_bounded_shadow_word_has_source_of_width` and `l1_bounded_shadow_word_has_source_of_width`, plus simple linear-budget wrappers `l0_bounded_shadow_word_has_source` and `l1_bounded_shadow_word_has_source`.

## Proof architecture

Write $w=L+m-z$. The abstract graph has the inductive invariant
$$z>0,\qquad w\ge4,$$
so for $m\le M$,
$$z\le L+m-4\le L+M-4<L+M.$$

The direct width hypothesis itself forces the exponent margin. Put $K=N-M-3$. Since $L\ge N+8$, we have $K+11\le L+M\le2^K$. If $K\le3$, then $2^K\le8$, a contradiction; hence $K\ge4$. Consequently $N-M-4\ge3$ and $N-m\ge2$ for every $m\le M$.

For the feeder range $N+8\le L\le N+9$, the simple linear budget $N\ge2M+7$ implies the width hypothesis: $K\ge M+4\ge4$ and
$
L+M\le N+M+9=K+2M+12\le3K+4\le2^K,
$
where $3K+4\le2^K$ for every $K\ge4$.

Consequently $z<2^{N-M-3}$. On an abstract edge $z=2^t r$, positivity gives $r\ge1$, hence $2^t\le z$, and therefore
$$t\le N-M-4,\qquad m+t+3\le N-1.$$
This is exactly the source safety margin required by `encoded_shift_divisible`, with one unit to spare.

Track an integer coefficient $\alpha$, initially 28 or 42, with edge update
$$\alpha'=\alpha+112\,2^m(2^t-1).$$
The invariant $28\le\alpha<56\cdot2^m$ is preserved. The source coordinate encoding is
$$2^m(b+4w)=\alpha\,2^N,
\qquad
b+4w=\alpha\,2^{N-m}.$$

It follows that the original left counter is large. Indeed, $m\le M$, $\alpha\ge28$, $w\le L+M$, and the width estimate give
$$b+4w\ge28\cdot2^{N-M},\qquad
4w\le4\cdot2^{N-M-3}.$$
Thus
$$b\ge440\cdot2^{N-M-4}.$$
The same coordinate encoding shows $4\mid b$, since $N-m\ge2$. In particular $b\ge12$, so any recovered inverse output has $k\ge2$.

## Excluding the non-iterable terminal counter

This is the delicate point. Odd parity alone does not exclude the terminal value $c=1$. The size estimate does.

Set $s=d+b/2+3$. Since the source second counter $d$ is odd, $d\ge1$, and the left-counter estimate yields
$$s\ge b/2+4
\ge220\cdot2^{N-M-4}+4
\ge6\cdot2^t.$$

The source divisibility lemma gives
$$2^{t+2}\mid(s+2z).$$
Using $z=2^t r$, we obtain $2^t\mid s$. Write $s=2^t C$. If $s+2z=2^{t+2}Q$, cancellation gives
$$C+2r=4Q,$$
so $C$ is even. The size inequality gives $C\ge6$. Therefore $c:=C-3$ is odd and $c\ge3$, and
$$s=2^t(c+3).$$
Thus the reconstructed inverse output is iterable; the exceptional $c=1$ branch is excluded by the full finite-size hypothesis, not merely by 2-adic parity.

## Recovering the exact original inverse

The exact power equation and `ancestor_exists_iff_power` produce a `GAncestor` witness. The completeness theorem `inverseAt_complete` then supplies an actual output `inverseAt b d t' = some (k,c)`. Applying `inverseAt_power` to that output and cancelling the positive factor $c+3$ forces $2^{t'}=2^t$, hence $t'=t$. The exact odd-cost equation supplies the source mass identity, and the existing `original_odd_edge_polynomial` transports the coefficient encoding to the child:
$$m'=m+t+1,\qquad
\alpha'=\alpha+112\,2^m(2^t-1).$$
The abstract next-node equation is precisely what makes the child left counter divisible by four. The same width estimate gives its positivity and the source hypotheses for the next induction step.

The feeder roots satisfy the required source mass and initial coefficient equations by `two_feeder_root_arithmetic`. The $L1$ root's oddness condition on $u$ follows from $u+4q+3=7\cdot2^N$.

## Scope

The current induction is formalized under the direct width inequality $L+M\le2^{N-M-3}$. The simple $N\ge2M+7$ feeder corollary is a convenient closed-form bound, not an optimal finite-window threshold.

This result would establish exact correspondence for every *fixed finite cost window* once $q\ge\lceil (2M+7)/16\rceil$. It does **not** establish:
- a lift of arbitrarily high cost at one fixed $q$;
- an infinite original-source inverse path;
- blank-tape forward reachability of any feeder state;
- P1 nonhalting or a BB(6) upper bound.

The current Lean file includes the full generic induction and both feeder corollaries, and the existing manual-only `agent9-p1-shadow-depth.yml` workflow now compiles it and prints its axiom audit. **Do not promote this to `results/` until that CI run passes and the source proof is independently checked.**
