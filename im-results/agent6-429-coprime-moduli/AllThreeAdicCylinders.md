# Every 3-adic second-counter class contains a synthetic BB429 halt

Agent 6, updated 2026-11-06. The all-natural derivation is now integrated into an unchanged-repository Lean source proof. The genuine blank-root machine #429 and BB(6) remain unresolved. See [ThreeAdicSynthetic.md](ThreeAdicSynthetic.md) and [successful source CI 42299330210](https://github.com/FlareZ123/bb6/actions/runs/42299330210).

## Statement

For every E≥1, every w∈Nat, and the full Agent5 twelve-branch source map `BB429.next/run`, there exist W,n,a,b∈Nat with

```
W % (3^E) = w % (3^E)
BB429.run n (0,W) = some (a,b)
BB429.next (a,b) = none.
```

These input states (0,W) are **synthetic**, never asserted reachable from blank (0,0). Consequently no forward inductive halt-free predicate containing (0,0), saturated under the second counter modulo any fixed power of three at exact first counter zero, can decide nonhalting via that quotient.

## Three proved-by-algebra synthetic families

The exact branch sequences and guard derivations are in [ResidueThreeTwoBurst.md](ResidueThreeTwoBurst.md); exact independent BigInt tests are in [ResidueThreeTwoBurstSFT.cjs](ResidueThreeTwoBurstSFT.cjs).

* For t≥1 define G2(t)=4·2^t−t; W2(t)=3G2(t)−13. Then (0,W2(t)) first-burst-halts after t macros; W2≡2(mod3).
* For q≥1 define G1(q)=16^q−q; W1(q)=24G1(q)−29. With t=4q+1, the orbit makes t first-branch steps, one even-counter odd-d reset, then t first steps to halt; W1≡1(mod3).
* For c≥2 define N(c)=4·2^c+c−10 and H0(c)=4·2^N(c)−8·2^c+13−c. Then W0(c)=3H0(c); after N(c) first steps, one odd-counter even-d non-first step, and 4·2^c−11 first steps, the orbit halts; W0≡0(mod3).

All three starting demands are nonnegative for their stated parameter ranges. Each prescribed non-first branch meets its exact guards. The complete source-map halting line is b+1=2a.

## Elementary lifting lemma

Suppose F(n) is an integer-valued sequence for n≥n0 such that for all e≥0, with p=2·3^e,

```
F(n+p) ≡ F(n)−p (mod 3^(e+1)).
```

Then F takes **every residue modulo 3^e**, for every e≥0, with a parameter n in [n0, n0+2(3^e−1)]. Prove this by induction. Modulus 1 is trivial. For an arbitrary target modulo 3^(e+1), pick a parameter matching the target modulo 3^e. The parameters n,n+p,n+2p have differences −p and −2p in F modulo 3^(e+1), which exhaust the three possible lifts because p=2·3^e. This extends the induction and adds at most 2p to the upper parameter bound.

The power congruence 2^(2·3^e)≡1(mod3^(e+1)) holds for all e: start from 2²=4≡1(mod3), and repeatedly cube 1+3^(e+1)z. It immediately proves the displayed shift identity for G2 and G1 because their power terms repeat after p and their linear terms contribute −p.

For H0, calculate the **exact integer identity**

```
N(c+p)−N(c) = 4·2^c(2^p−1)+p.
```

Since 3^(e+1) divides 2^p−1, the right side is divisible by p=2·3^e. Hence 2^N(c+p)≡2^N(c)(mod3^(e+1)), while also 2^(c+p)≡2^c(mod3^(e+1)). Only the −c term changes, giving H0(c+p)≡H0(c)−p. Thus all three functions satisfy the lifting lemma.

## Completion

Fix a target residue r modulo 3^E and let M=3^(E−1). If r≡2(mod3), choose t≥1 with G2(t)≡(r+13)/3(modM), giving W2(t)≡r(mod3^E). If r≡1(mod3), choose q≥1 satisfying 8G1(q)≡(r+29)/3(modM), possible because 8 is invertible modulo M; this gives W1(q)≡r. If r≡0(mod3), choose c≥2 with H0(c)≡r/3(modM), giving W0(c)≡r. These choices exist by the preceding lifting lemma, so each residue has a genuine synthetic **full-source-map** halting trajectory.

The parameter bounds are t,q≤2·3^(E−1)−1 and c≤2·3^(E−1). The full numerical starts can be astronomically large, but each is a finite natural number and has a finite source-level trajectory.

## Status

The uniform all-3-adic statement and its invariant obstruction are now Lean-kernel checked against the unchanged repository modules by [ThreeAdicSynthetic.lean](ThreeAdicSynthetic.lean). The final theorems depend only on [propext, Classical.choice, Quot.sound], with no sorryAx or custom axiom; the reproducible manual-only source workflow passed at [CI 42299330210](https://github.com/FlareZ123/bb6/actions/runs/42299330210). The finite independent simulations remain corroborative rather than proof dependencies. The separate 27-class Lean theorem BB429Full27.lean retains its own earlier source-status boundary. This all-3-adic result is a **method obstruction**, with no rooted blank decision or BB(6) bound. No external priority is asserted.
