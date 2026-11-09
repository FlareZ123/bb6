# High-cost P1 fixed-shadow gateway cylinders (9 Nov 2026)

The proof-data generator [generate_large_rows.py](generate_large_rows.py) computes exact finite source-shadow closures of the P1 recurrence, validates node counts and budgets, emits per-cost-row Lean closure certificates and invokes the pre-existing genuine-original-source theorem `BB6.Agent9UniformParamK.universal_blank_critical_cylinder_param_K_of_predicates`. A certified base q with parameters B,K excludes `Reach 2 (14*2^(16*(q+2^(B+K)*r)+2)-2*(16*(q+2^(B+K)*r)+2)-10)` for **all natural r**. No raw machine decision or BB(6) bound follows.

## Original-source Lean certified q classes

The terminal `BB6.Agent9Q<q>.no_critical_gateway` theorem is checked under pinned Lean 4.36.0-rc2, with only `[propext, Classical.choice, Quot.sound]` axioms, and no sorry.

| q | B | K | Source CI |
|---:|---:|---:|---|
| 38 | 249 | 10 | [42597508228](https://github.com/FlareZ123/bb6/actions/runs/42597508228) |
| 45 | 401 | 11 | [42596254597](https://github.com/FlareZ123/bb6/actions/runs/42596254597) |
| 101 | 769 | 12 | [42597508228](https://github.com/FlareZ123/bb6/actions/runs/42597508228) |
| 113 | 227 | 11 | [42596254597](https://github.com/FlareZ123/bb6/actions/runs/42596254597) |
| 129 | 355 | 12 | [42597508228](https://github.com/FlareZ123/bb6/actions/runs/42597508228) |
| 146 | 729 | 12 | [42597508228](https://github.com/FlareZ123/bb6/actions/runs/42597508228) |
| 189 | 691 | 12 | [42597508228](https://github.com/FlareZ123/bb6/actions/runs/42597508228) |
| 273 | 365 | 13 | [42597508228](https://github.com/FlareZ123/bb6/actions/runs/42597508228) |

A separate successful original-source batch [42598520595](https://github.com/FlareZ123/bb6/actions/runs/42598520595) certified **15 additional** base q values `46,49,54,58,62,66,78,81,82,85,86,90,94,97,98` (K=12, common family B per q specified in generator). These combine with prior existing finite-root certificates to eliminate **all q in the finite interval 29≤q≤100** for the necessary gateway `n=16q+2`. The 15 were absent from the earlier 701/1024 census; rigorous external novelty remains unreviewed.

**Uncertified q294:** exact shadow BFS numerically gives 161,223 and 160,455 nodes with B=2515 and K=13, but Lean's row evaluator exhausted recursion resources in CI 42597508228. No theorem for this q is claimed. The generator retains this reproduction target; a more scalable certificate representation is needed.

Manual-only CI workflows: [largecones](../../.github/workflows/agent9-p1-largecones.yml), [seven-cones](../../.github/workflows/agent9-p1-seven-cones.yml), [small-gaps](../../.github/workflows/agent9-p1-small-gaps.yml). The original `checkRow` and original-source reachability bridge are reused without modifications. Generated data is checked by Lean; Python output alone is not a proof.

See [the universal two-pile representation](../agent9-p1-binary-heaps/README.md) for the independent structural result. All work here is intermediate: six-state Busy Beaver BB(6) remains open.
