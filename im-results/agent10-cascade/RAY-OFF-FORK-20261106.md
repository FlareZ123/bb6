# #746 arbitrary-depth odd-fork root pruning (Agent 10, 2026-11-06)

## Source-certified scope

This is a **blank-root-sensitive, uniform** result about the exact first-return source-C model of Cryptids machine #746. It is currently an intermediate research result, with open higher-valuation branches. It does not establish nonhalting, a BB(6) upper bound, or the exact Busy Beaver value. The exported Lean theorems under this folder were checked from the original imported source chain by manually dispatched Lean 4.36.0-rc2 GitHub Actions; final `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

- [RayOddForkStrip.lean](RayOddForkStrip.lean): `source_tone_ray_fork_dead`, arbitrary ray depth and an exact depth-12 case. [Source CI 42134596250](https://github.com/FlareZ123/bb6/actions/runs/42134596250), success.
- [RayOddForkExtended.lean](RayOddForkExtended.lean): `narrow_gap_no_reset_parent`, `source_tone_ray_fork_dead_either`; crucial residue-two correction and a depth-16 case. [Source CI 42135044167](https://github.com/FlareZ123/bb6/actions/runs/42135044167), success.
- [RayForkStripSelect.lean](RayForkStripSelect.lean): `odd_root_exact_high_gate`, genuine **iff** reduction with all odd-parent witnesses retained; t=0 absent, t=1 exceptional gates only, all t≥2 kept. [Source CI 42136190557](https://github.com/FlareZ123/bb6/actions/runs/42136190557), success.
- [RayPacketHigh.lean](RayPacketHigh.lean): `exact_high_packet_root_reduction` composes the preceding iff with Agent 7's exact six-packet fork selector. Its first source CI remains to be checked; do not claim upstream verification until the run succeeds.
- [ray_fork_strip_scan.py](ray_fork_strip_scan.py): optional deterministic synthetic candidate census, **not** a proof tool.

## Uniform geometry and exact inverse-parent mechanism

Let `n≥13`, `n%6∈{4,5}`, any ray depth `j`, `P=2^n`, `D_j = 2^j(2n+3)-(n-1)` (equivalent to Agent 7's recursive `deficit`), `U_j=4P-D_j`, and assume the explicit **sufficient** high-margin condition

```
32*D_j + 64*n + 128 <= 2^n.
```

At any exact odd-branch source witness with `t=1`, the odd dyadic scale is necessarily `k=n-2` (independent of `j`), and for witness odd `d` and parent `h`:

```
2*U_j + 5 = 9*d,
4*d = 8*2^(n-2) + h + (n-2) + 5,
9*h + 8*D_j + 9*n + 7 = 14*P.
```

The only even reset parent of `h` is `w=2*h-2*P-(n-2)`. The margin places `h` into the unique scale-`n-2` even-image band, its potential odd `t=0,1` inverse values in prohibited odd-image gaps, and `w` in the **narrow dyadic gap**

```
P < w,      8*w + 32 < 9*P.
```

Thus, when `(2h+5)%27 != 0`, no source odd parent of `h` exists and **every genuine root path to `h` must pass through `w`**. The narrow gap excludes all even parents of `w`. It also excludes odd `t=0` parents; any odd `t>=1` parent requires `9 | (2w+5)`. Consequently `w` has no blank-root reachability if

```
w%3 != 2    OR    (2*w+5)%9 != 0.
```

For surviving `n%6∈{4,5}`, the first disjunct is implied by `h%3 != 0`. The resulting source theorem proves absence of every `t=1` odd fork whose `h` satisfies

```
(2*h+5)%27 != 0
AND
(h%3 != 0 OR (2*w+5)%9 != 0).
```

The `w%3=2` case is a **genuine extra** root obstruction relative to the previous fixed-`j=4` result. All hypotheses are explicit, natural-number equations, with `ReachC (2,0) (h,0)` from the actual post-initial root.

`odd_root_exact_high_gate` lifts this to the complete, not truncated, odd inverse grammar: an actual rooted odd fork must have either `t>=2`, or `t=1` with `27|(2h+5)`, or `t=1` with **both** `h%3=0` and `9|(2w+5)`. Each permitted branch remains a genuine source witness: the theorem invents none, and its reverse implication is immediate from the retained original witness. Source-certified [run 42136190557](https://github.com/FlareZ123/bb6/actions/runs/42136190557).

## Deterministic exploratory census (not a density theorem)

Run `ray_fork_strip_scan.py` with Python 3.11+. It considers n=13..600 in surviving residue sectors, every physical depth meeting the explicit sufficient margin, and every exact source-algebraic `t=1` odd fork. It finds 9,623 synthetic `(n,j)` candidates, of which **8,193** satisfy the uniform Lean hypotheses and **1,430** require further work. The remainder splits into 1,071 cases with `h%3=0, 9|(2w+5)` and 359 cases with `h%3=2, 27|(2h+5)`. Their presence in the inverse grammar is no evidence of actual rooted reachability, and the finite counts imply no asymptotic density theorem.

A depth-12 example: n=23, j=12, h=12,870,538 has source-certified `¬ReachC (2,0) (h,0)`. A new hard-residue example: n=35, j=16, h=53,444,229,342 has `h%3=0` yet is excluded by the new residue-two gap proof. Both are illustrative instances of the uniform result, not new fatal-height exclusions.

## Next authentic obstacles

1. At a narrow-gap `w` with `9|(2w+5)`, inspect the exact `t=1` odd parent at scale `n-4`, and preserve any `t>=2` cases when `27|(2w+5)`. Some admissible parents have forced even-return runs leading to another prohibited gap. A geometric high-margin all-depth proof might exclude an additional infinite sector.
2. When `27|(2h+5)`, inspect all legitimate `t=2,3,...` parents of `h`, especially the depth-four 3-adic cases already seen in fixed-`j=4` work. No unilateral parent elimination is valid without considering every possible higher valuation.
3. Feed `odd_root_exact_high_gate` and `exact_high_packet_root_reduction` into Agent 7's `PacketSelector` six-packet programme. Continue preserving the disjunction with the canonical continuation branch, which remains unresolved. A universal BB(6) conclusion additionally requires covering other holdouts and obtaining a global upper bound.

The theorem uses existing exact source-C `ResetParent`, `ResetChain`, `root_reset_chain_iff`, and gap/odd-band results from Agents 7 and 10; mathematical novelty beyond this repository needs external peer comparison. The correct destination until such assessment is `im-results/`.
