# Raw108: exact weighted maximum 4,136,175

For the six-state binary partial transition table

```
1RB---_1RC---_0RD---_1LD1RE_---1LB_------
```

there are six undefined rows and 25^6 = 244,140,625 literal completions (24 ordinary actions and one halt per row). For every compatible completion, every halting ordinary execution of length k and every admissible incoming blank delay d satisfy d+k+1 ≤ 4,136,175. The bound is attained with k=4,136,174 and d=0. This is a local weighted maximum, not an exact value of BB(6).

The theorem `BB6.Agent10Raw108Exact.exact_bound (B : Nat)` states that the universal `WeightedBound B` over all compatible machines holds iff 4136175 ≤ B. See [Raw108Exact.lean](../im-results/agent10-raw108/Raw108Exact.lean), [attainment](../im-results/agent10-raw108/Raw108LongAttained.lean), and the [complete construction](../im-results/agent10-raw108/README.md).

The original-source Lean 4.36.0-rc2 kernel accepted all 19 pinned proof shards, the conservative upper bound 4,136,180, and the sharp parent theorem in [run 45788380944](https://github.com/FlareZ123/bb6/actions/runs/45788380944), source revision e40934b3e1211b36fd617377f81c3658b23ebffd. The theorem's axioms are limited to propext, Classical.choice, and Quot.sound. Exact artifact 15100918710 SHA-256 63e53860e4bc6fb000bc41ade65d5278232290a604b09e91554e47ebcf4ffb35. Conservative artifact 15101731441 SHA-256 77f7274d51f16697b29bcf2fbee1eb25ed3a2084b1e5134e36bd6e3759e6d21c. [Pinned input manifests](../im-results/agent10-raw108/accepted-pins.json) permit reproduction using the existing manual raw108-compose target.

The proof uses translated cycles, first-hole bounds, ordinary and block FAR certificates, and parametric positive-return inductions. The sharp bound replaces only the weight cutoff on the already checked audit. No timeout counts as evidence of nonhalting. Agent31 received the parent certificate for the shared canonical integration; membership and consumer acceptance are separate obligations.
