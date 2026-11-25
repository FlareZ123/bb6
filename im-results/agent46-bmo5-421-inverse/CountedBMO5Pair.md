# Common exact primitive score of the three BMO5 holdouts

The shared unweighted rooted graph is described in README.md. Here the same graph carries a single exact integer weight for all three literal transition tables. All counts include the final undefined query.

For #252, write A2(a,b,c) with state A, left near-first (01)^(a+1) 11 (01)^b, and right near-first 1^(c+1). #754 is the state conjugate A→B→C→A with D/E/F fixed, so the same coordinates apply. Their blank arrivals are 54 moves to A2(0,1,6) and 30 moves to A2(0,1,2) respectively, in common coordinates.

| Source | Destination | Primitive count |
|---|---|---:|
| A2(0,b,0) | A2(0,1,2b+10) | 14b+87 |
| A2(a+1,b,0) | A2(a,b,1) | 2 |
| A2(a,b,1) | A2(0,1,4a+2b+14) | 4a²+4ab+44a+18b+125 |
| A2(a,0,2) | undefined query | 8a+30 |
| A2(a,0,4) | A2(0,1,2a+12) | 14a+91 |
| A2(a,0,c+6) | A2(0,a+4,c) | 8a+34 |
| A2(a,b+1,c+2) | A2(a+2,b,c) | 4a+12 |

The simultaneous k-step diagonal drain costs 4k(a+k+2). The relevant section is A2(0,1,2(x−2)) for x≥2. Its successor is exactly Cap.f(x). Its primitive count equals Counted421.score(x) when the successor exists and is twelve smaller for the terminal section. This follows by composing the counted rules, not fitting sample runtimes.

Put T_i=Cap.halt(i) and W_i=Counted421.arrivalCost(T_i)+Counted421.score(T_i). The common exact weighted terminal formula is

| Machine | Root requirement | Count including final query |
|---|---:|---:|
| #252 | rootOf(T_i)=1 | W_i+3 |
| #421 | rootOf(T_i)=2 | W_i+8 |
| #754 | rootOf(T_i)=3 | W_i+18 |

The #252 offset accounts for the synthetic predecessor 1→5 of weight 39: 54−39−12=3. The #754 offset is 30−12=18. These are iff criteria; they do not establish existence or nonexistence of a terminal on any of the three roots.

## Proof artifacts and status

- CountedBMO5Pair.lean: literal tables, conjugacy, all counted macro rules and initial sections; local Lean 4.36.0-rc2 completed with only standard axioms, blob 0fc52829ee72829056ac984d9ccfc83455523342.
- CountedBMO5PairDrain.lean: exact weighted drain and shared score identity; local Lean completed against verbatim Cap.drain/f and Counted421 cost definitions, standard axioms only.
- CountedBMO5PairScore.lean: common ancestry and iff of exact blank halt scores. Local elaboration passed against the existing proved interface statements supplied as temporary assumptions; those assumptions are not in the repository. The committed modules import the real dependency closure, and the extended existing counted workflow will check that closure. Source acceptance is pending.
- The full Frontier transport for #252 and #754 and a uniform weighted upper bound independent of the root are still to be provided. No leaf has been newly discharged.
