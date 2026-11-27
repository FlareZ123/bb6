# Deterministic reverse test for the P1 critical boundary

**Status:** original-source Lean 4.36.0-rc2 proof in [ReverseGuard.lean](ReverseGuard.lean), accepted at f4b1462c774be61e8db33ff68db35dc002c9eb85 by [CI 46047767028](https://github.com/FlareZ123/bb6/actions/runs/46047767028). This is not a P1 or BB(6) decision.

## Exact inverse branch

Let T=7·2^n. At cost m, an original guarded micro endpoint (v,w) has v+w+n+m+1=T. Every positive-cost endpoint has v≥2 and w≥5. The initial endpoint at cost 0 is (1,T−n−2). For an endpoint (v,w) at cost m>0, algebraically inverting the unit equations gives the two candidate predecessors:

* selected bit 1: (v−w+1,2w);
* omitted bit 0: (2v,w−v+1).

The former requires w≥5 and v≥w, as its parent right coordinate must be positive. The latter requires v≥2, m>1, and w≥v+4, because its parent left coordinate is at least five. Thus there is at most one legal predecessor at every positive cost. The remaining band w−v=1,2,3 is impossible. Equality v=w can occur only at m=1 (the compulsory initial split): its sole legal predecessor has right coordinate one, forbidden at all positive costs.

The Boolean recursion tests these exact branches and the original root. The reverse direction is not merely a relaxation: each accepted predecessor satisfies the original guarded unit equation by the conserved mass. Induction gives an iff for every n≥14 and every cost, and the terminal guard w≥6 then gives the full LegalGap relation. It follows that guarded endpoint histories have a unique reverse branch sequence. This differs from the earlier right-five-only FirstReturn interface: it handles any endpoint and its actual asymmetric guards, including the unfinished last gap.

The source bridge consumes the three necessary boundary families from [LagBoundary.lean](LagBoundary.lean) (accepted source CI 46033272360): w≤10; v=2 with n+m even; or v odd ≥5 and w+floor(v/2)=7·2^j for j<n. Excluding the Boolean test on all such positive-cost, w≥6 endpoints excludes the authentic critical reset, without a delayed-word cutoff. The universal boundary exclusion itself remains open.

## Exact reverse blocks (kernel accepted)

For a run of k omitted bits, the reverse endpoint is (2^k v, v+w+k−2^k v). If k<m, v≥2 and 2^k v+5≤v+w+k, all k reverse zero steps are legal as far as their local guards are concerned: the left-minus-right difference strictly decreases as the reverse run length increases, so the last guard is strongest.

For k selected bits, the reverse endpoint is (v+w+k−2^k w,2^k w). If k≤m, w≥5 and 2^k w+1≤v+w+k, all k reverse one steps satisfy their local guards for the same monotonicity reason. The exact recursive check on the remaining endpoint is unchanged. These formulas give a logarithmic-search run jump; the generic jump identities are kernel-checked. A separate efficient maximal-run implementation is future work.

A reverse test of a single endpoint is not a simultaneous proof for exponentially many costs. The advantage is elimination of all word ambiguity at a specified endpoint, and a route to a symbolic interval checker for the boundary families; it does not prove the all-index exclusion. Existing delayed-carry certificates remain the preferred method for broad finite ranges.

Local Lean execution was unavailable in this invocation (container and Python ClientError before execution). The existing manual exact-lag workflow is reused for focused source acceptance; no new workflow is introduced.

## Wide delayed-carry numerical result (distinct from the endpoint checker)

For n=814324766, the conservative half-prefix carry computation terminated with an empty cover at K=1628649533=2n+1, exit 0. This is a new numerical result, not a kernel certificate. The previous checkpoint came from [run 46031445049](https://github.com/FlareZ123/bb6/actions/runs/46031445049); the continuation [46047244477](https://github.com/FlareZ123/bb6/actions/runs/46047244477) used h=n/2, budget 3257299064, P1_FUSE=16, P1_PLAN=1, P1_JUMP=26, two OpenMP threads. The summary-only [run 46048015879](https://github.com/FlareZ123/bb6/actions/runs/46048015879) read the existing output without repeating the computation and produced artifact 15222698900 named n814-end-1628649533-exit-0. The result falls below the proved practical crossing cutoff, so a kernel-checked matching cover would exclude this index at the original critical reset. Neither the binary checkpoint nor AVX512 calculation is an accepted Lean proof. The remaining all-index and authentic blank-root quantifiers are not closed.
