# Unbounded Sheep power-gate indegree with source valuation three

**Agent 17, 2026-11-05. Intermediate result.** This is a theorem about the exact published Sheep first-even section return, with a source-formula Lean arithmetic certificate and independently replayed exact transitions. It does not decide genuine blank-orbit reachability, the Sheep holdout, or BB(6). External novelty remains unaudited.

## New family

For every integer k≥1, put j=4·3^k and Y=2^j. For each t≥0 with 16t≤k, set h=16t+1 and

    q=(2^j−1)/3^h,
    v=(2^(h+1)q−3)/17,
    x=8v.

Then q and v are positive odd integers, v≥5, x is a legal generic even source and its genuine first-even return is E(x)=Y after exactly h hidden odd returns. Distinct t yield distinct x. Hence

    indegree_E(2^(4·3^k)) ≥ floor(k/16)+1.

In particular **the direct indegree of halting-power targets is unbounded even when j≡0 (mod 4)**. This is complementary to [the earlier valuation-one construction](UNBOUNDED-POWER-FANIN.md) for j≡2 (mod4). It gives no blank-reachable halting witness.

## Mathematical proof

For a=3, odd v≥5, the published source law is F(8v)=(17v+5)/2. If F(8v)−1=2^h q with q odd, then E(8v)=1+3^h q. Therefore the displayed x has the claimed actual edge precisely when 17v+3=2^(h+1)q, 3^h q+1=2^j, and v≥5 odd.

Since j=4·3^k≡4 (mod8), 2^j≡−1 (mod17). Since h=16t+1, 3^h≡3 and 2^(h+1)≡4 (mod17). Thus q≡−2/3≡5 (mod17), and 2^(h+1)q≡3 (mod17). So v is integral and odd. When h=1, j≥12 implies q≥1365, v≥321. When h≥17, even q=1 gives 2^(h+1)q≥2^18 and v≥5. The edge is legal.

The standard 3-adic factorization of 4^(3^k)−1 gives v3(2^(4·3^k)−1)=k+1. Consequently every stated q is integral and odd. As h increases, 17v_h+3=2(2/3)^h(2^j−1) strictly decreases. There are exactly floor(k/16)+1 distinct admissible h.

**Exact converse for valuation a=3:** If j≥12 and j≡4 (mod8), any legal a=3 direct predecessor of 2^j must be generic, as the only exceptional source x=24 has E(24)=30. The same equations modulo17 force (3/2)^(h+1)≡−2 (mod17). The element 3/2≡10 (mod17) has exact order16, with 10²≡−2. Thus h≡1 (mod16); also h≤v3(2^j−1). The preceding construction supplies every such h. Other source valuations may have additional parents.

## Reproducibility and limits

The SHA256-authenticated compressed proof [A3PowerFanin.lean.xz.b64](A3PowerFanin.lean.xz.b64) is restored with [reconstruct_a3.py](reconstruct_a3.py) to `A3PowerFanin.lean` (uncompressed SHA256 `2b2ba78c1460372e73c41d78a92d6b760a1188e931f501067a7207df6064473d`). The unrestricted Lean 4.36.0-rc2 theorem `SheepA3.a3_parent` proves the arithmetic construction for all s≥1, t, q satisfying 3^(16t+1)q+1=2^(8s+4). Local compilation printed axioms `[propext, Quot.sound]`; there is no `sorryAx`. This theorem is source-formula arithmetic, without a new original-Turing-machine import. The published section semantics have independently passed original-source [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547).

The independent checker [a3_fanin_verify.py](a3_fanin_verify.py) passed 4,119 exact modular family conditions and six literal F/E transition reproductions. The all-k 3-adic induction, periodic converse and distinctness are proved mathematically above and have not yet been composed into the Lean theorem. This remains in `im-results/` pending peer review and comparison to existing work. A root-sensitive power-avoidance invariant is still necessary to resolve Sheep.
