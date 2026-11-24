# A well-founded potential for first-hole queue expansion

**Status:** conditional algorithmic lemma for the weighted-TNF programme. This is not a BB(6) upper-bound proof and does not certify the upstream queue implementation.

## Setup

Let (Q) be a finite queue of sparse partial tables. Let (u(p)) be the number of unassigned transition slots in a queued node (p). A first-hole expansion removes one node (p) and does one of two things:

1. classifies (p) and enqueues no children; or
2. replaces (p) by a complete family of children, each obtained by assigning the current hole, hence each with exactly (u(p)-1) unassigned slots.

For canonical TNF expansion at support cut (c), the ordinary children are indexed by
[
(w,dir,q),quad w,dir\in\{0,1\},quad q<c,
]
and the fresh-label children by ((w,dir)) with successor (q=c). Thus there are exactly (4(c+1)\le28) ordinary children when (c\le6). If an implementation separately enqueues the halt branch, the total is at most 29.

## Potential

For a safe uniform branch bound of 29, define
[
\Phi(Q)=\sum_{p\in Q}30^{u(p)}\in\mathbb N.
]

If a node with (u=u(p)>0) is classified, its contribution (30^u) disappears. If it is expanded into at most 29 children, their total contribution is at most
[
29\cdot30^{u-1}<30^u.
]
All other queue entries are unchanged. Therefore every queue update strictly decreases (\Phi). Since (\mathbb N) is well-founded, no infinite sequence of such updates exists. Starting from one node with (u_0) holes, the number of updates is bounded by (30^{u_0}).

The base 30 is deliberately conservative. If the source queue uses all 24 ordinary instructions and handles halt separately, base 25 suffices; if it includes the halt option as a queued branch, base 26 suffices. The canonical TNF bound gives 28 ordinary children, or 29 including halt, so base 30 covers either convention.

## What this does and does not establish

This is a clean termination argument for a queue that actually removes one node and either classifies it or replaces it by its complete first-hole expansion. It is independent of the soundness of any decider.

It does **not** establish that the pinned `Enumerate62.v` implementation satisfies those assumptions. In particular, the exact `SearchQueue_upd` code must be checked for requeueing, unchanged nodes, duplicate bookkeeping, and whether every child adds exactly one assigned slot. The potential also does not prove that a computed holdout list is exhaustive unless the update's coverage invariant is proved.

The local coverage obligation is precisely the one formalized by `WeightedTNFCertificate.expand`: for every compatible total machine, the current hole is either the halt case (discharged by the first-hole weighted bound) or one of the canonical ordinary children. The remaining source-level work is to connect the actual queue update to this complete branch family and prove the queue's initial-to-final coverage invariant.

## Suggested formalization

After importing the exact upstream queue representation, define its hole count and queue potential. Prove a local lemma for each `SearchQueue_upd` case:

- a classified node contributes no replacement queue entries;
- an expanded node contributes at most 29 entries, each with one fewer hole;
- no update leaves the selected node unchanged or requeues it without progress.

Then derive strict decrease by `Nat.pow_succ` and `omega`, and use well-founded recursion on (\Phi) to prove queue drain. Keep the independent machine-coverage theorem separate; termination alone is not exhaustiveness.
