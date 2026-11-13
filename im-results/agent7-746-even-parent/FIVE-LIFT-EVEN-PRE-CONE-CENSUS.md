# Even fatal-predecessor reverse cones on five stable 887 lifts

**Status: exact-integer computational census; only the n=887 list has a Lean certificate draft, and that draft has not yet compiled in CI. No five-lift source theorem is claimed.**

## Target and exact parent grammar

For the fatal target at index n, the displayed even first-reset predecessor is

`evenPre(n) = 4·2^n − 3n − 7`.

The exact source-C reset predecessor relation is the disjunction in `CascadeResetInverse.ResetParent` (`im-results/agent10-cascade/FirstInverseComplete.lean`). For a target u:

- An even parent exists exactly when `6·2^k−1 ≤ u ≤ 8·2^k−3`; its height is `h=2u−8·2^k−k`.
- For every t with `3^(t+1) | 2u+5`, put `d=(2u+5)/3^(t+1)`. An odd parent exists exactly when d is odd and `x=2^t d` lies in an odd band `6·2^k+1 ≤ x ≤ 8·2^k−1`; its height is `h=2x−8·2^k−k−5`.

The enumerator `enumerate_even_pre_cones.py` implements these two untruncated formulas using arbitrary-precision integers. It performs reverse BFS until every generated state has no further parent. This is an exact-integer computation, not a Lean proof; `ParentsFast.lean` and `ClosedCertFast.lean` provide the corresponding formal checker and soundness theorem.

## Same-scale even spine

Write `y_m=4·2^n−D_m`. The target has `D_0=3n+7`; its same-scale even parent gives

`D_(m+1)=2D_m+n−1`, hence `D_m=(4n+6)·2^m−n+1`.

The state y_m remains in the scale-(n−1) even band exactly while `D_m≤2^n+1`. The full reverse cone consists of this long deterministic spine together with odd-parent side branches and their recursively generated parents.

## Exact-integer census

The five n values below are the stable subresidues identified in Agent 44's modular table: `n mod 13122 ∈ {887,2345,5261,6719,11093}`. The enumeration found a rooted tree in every case: `edges=nodes−1`, zero repeated/merging parents, and no occurrence of root height 2.

| n | cone nodes | leaves | main even spine | off-spine nodes | max depth | largest side branch (nodes/depth) | max v₃(2u+5) | max odd t |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 887 | 1,319 | 181 | 876 | 443 | 876 | 15 / 10 | 7 | 6 |
| 2345 | 3,536 | 480 | 2,332 | 1,204 | 2,332 | 22 / 11 | 9 | 8 |
| 5261 | 7,943 | 1,077 | 5,247 | 2,696 | 5,249 | 23 / 12 | 8 | 6 |
| 6719 | 10,191 | 1,390 | 6,705 | 3,486 | 6,706 | 49 / 25 | 8 | 6 |
| 11093 | 16,833 | 2,289 | 11,078 | 5,755 | 11,078 | 39 / 18 | 8 | 6 |

Additional edge counts are 1,318; 3,535; 7,942; 10,190; and 16,832 respectively. Odd-parent edges leaving the main spine number 162; 433; 975; 1,245; and 2,058. Total odd-parent edges, including those inside side branches, number 216; 581; 1,303; 1,684; and 2,777.

### Independent match at n=887

The generated n=887 set agrees exactly with the 1,319 hexadecimal entries in `EvenPre887Cone.lean`: zero computed nodes are missing from the Lean list and zero Lean entries are extra. The committed Lean draft asserts `closedCertFast evenPre887Cone = true`, membership of the target, and absence of 2, then derives `¬ ReachC (2,0) (evenPre887,0)` via `closedCertFast_excludes`. This is the correct source-root proof architecture, but the draft is **not yet CI-verified**.

## What this does and does not establish

- For n=887, the finite list is a candidate kernel-checkable reverse-cone certificate for the even fatal predecessor. If the existing Lean module compiles and its axiom audit is clean, it proves this one fixed target unreachable from the authentic post-initial source-C root.
- For n=2345, 5261, 6719, and 11093, the exact-integer computations find the same no-root phenomenon, but no corresponding Lean list/certificate has been checked.
- The fatal-target-to-even-predecessor reduction also needs its odd-feeder branch formally extended to these four lifts. Agent 44's five-lift residue table is computational support; the current `FeederExceptional887.lean` theorem is restricted to `n mod 13122 = 887`.
- These five representatives do not cover the four other lifts over `n mod 1458 = 887` (k=2,5,6,8), whose odd-feeder trees have deeper, changing topology.
- The largest side branch is not uniformly bounded by the n=887 example: n=6719 already has a 49-node, depth-25 branch. A family proof must handle the nested 3-adic structure; extrapolating the six-node feeder or the small n=887 side branches is invalid.

## Next mathematical step

Replace the explicit finite list by a symbolic description of the even spine and all odd side branches. The Hensel selector should classify the indices m at which `2y_m+5` acquires each 3-adic valuation; each resulting odd parent then needs an exhaustive recursively rooted classification. A uniform theorem must quantify over n, not merely over these five representatives.

Keep this work in `im-results/`. It is an intermediate #746 root-exclusion programme, not a publishable BB(6) result and not a solution of BB(6).

— Agent 7
