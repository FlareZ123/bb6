# Raw139 E1=0RD/D0=1LF: nine-spine, 206-region source strategy

**28 November 2026 — intermediate structural and certificate engineering result.**
The exact Raw139 parent has 31,277 finite first-query splits and 4,875
cutoff-100 open children, of which only two are exceptional. Replay of the
original finite-tree simulator at cutoff 100, FAR depth 2, and the saved
parent table `[7,24,11,24,14,24,22,16,24,13,24,24]` partitions the
full source tree into **9 split nodes on the exceptional spines** and
**206 pairwise disjoint ordinary subtree regions**:

| Exceptional leaf | 24-branch path through the finite source tree | Status |
|---|---|---|
| 2265 | `[12,6,5,3,20]` | Exact 228-digit E0 first query source certified |
| 3506 | `[13,18,8,3,0]` | F067 tower project, independent ongoing source effort |

The paths branch at the root. Each has five decision nodes, so their union
contains exactly `5+5−1=9` query nodes; each such node has 24 children,
of which either one or two continues to an exception. Thus the ordinary
frontier has **206** disjoint roots `9·23−1 = 206`.
Every one of the other 4,873 open leaves occurs beneath exactly one of
these ordinary roots.

The finite data counts are **542,177** cyclic leaves, **146,564**
last-missing-instruction leaves, **25,756** FAR leaves, and **31,277**
split nodes. The **4,873** ordinary open recipes are 4,482 block/automaton,
378 final-query, eight one-split graft, and five cycle recipes. The same
`206+9` partition covers all of these without replaying the ordinary
subtrees in each downstream hybrid proof.

## Reproducible computation versus Lean proof

1. `plan-two-exception-spine.py` recompiles and replays
   `im-results/agent48-raw139-e0-0re/replay.cpp`, checks the complete
   ordered 4,875 child table list and all aggregate counts against the
   frozen `census-d0lf1.json`, follows the two exact five-deep paths,
   verifies every exceptional leaf, and derives the 206 ordinary regions
   from all other sibling branches. This exact replay passed
   [CI 46151218241](https://github.com/FlareZ123/bb6/actions/runs/46151218241)
   and published JSON [artifact 15265488529](https://github.com/FlareZ123/bb6/actions/runs/46151218241/artifacts/15265488529).
   This is a reproducible finite **computation**; by itself it is not
   the mathematical proof of the parent Cover.
2. `emit-two-bound-spine.py` deterministically emits an original-source
   Lean theorem with the literal parent table, nine explicit
   `TwoBoundAudit` splits, 206 **explicit audited** ordinary finite
   subtree hypotheses, the fully source-accepted child2265 Cover
   `leaf2265_cover_at_large`, and a single independent F067 child3506
   `WeightedBound largeBound` hypothesis. Each split query and table
   identity is demanded by the original physical-run kernel checker.
   The generated `parent_cover_conditional` yields
   `Cover (WeightedBound (2^32768))` for the parent, under only those
   declared premises, and `lift_hybrid_cover` transports it to the
   already-attained champion bound without computing the enormous exponent.
3. `.github/workflows/agent3-d0lf1-conditional-spine-source.yml`
   regenerates the entire source and compiles its full original-source
   closure with pinned Lean 4.36.0-rc2. **Until this CI has succeeded**,
   the nine-spine conditional statement remains a candidate. The first
   run [46151524781](https://github.com/FlareZ123/bb6/actions/runs/46151524781)
   failed due a generated ambiguous `check` identifier, fixed in
   commit `66223bf6`; rerun `46151793808` was dispatched.

## Next strict mathematical obligations

The 206 ordinary subtree proofs are independent original-source
`packedPrefixCheck 148142 (regionTable i) (audits i) = true`
computations. Their actual audit tree data, FAR certificates and any
one-split grafts must be generated from the frozen source, source-checked,
and then combined into one `CheckedAudits` proof. Their number is small
enough to distribute in shards. The F067 child3506 source proof remains
separate, potentially higher priority than arbitrary finite sharding.
Once both are accepted, `parent_cover_conditional` immediately yields
one complete Raw139 D0=1LF branch Cover at the attained champion score.
This still does not by itself close the full Raw139 parent, other E1/D0
branches, the 39 global Canonical Cover hypotheses, or BB(6).

The numerical source tree, 206-region partition, and conditional theorem
are located in `im-results/` because only the already-source-checked
index2265 proof is presently an academically publishable resolved
machine result.
