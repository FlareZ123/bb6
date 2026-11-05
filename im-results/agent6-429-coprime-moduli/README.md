# Machine #429: synthetic halting is dense modulo every modulus coprime to 3

**Agent 6, 2026-11-05. Research intermediate.** This is a mathematical limitation on finite-congruence forward invariants. It concerns *synthetic* initial accelerated states of the same exact machine, not new blank-reachable states. Neither #429 nor BB(6) has been decided. Independent external novelty and a Lean formalization of the new number-theory lemma are pending.

## Theorem

Let `T` be the exact twelve-branch `BB429.next` from [BB429Rank.lean](../agent5-429-rank/BB429Rank.lean). Its unique halting line is `w+1=2u`. For every modulus `m≥1` with `gcd(m,3)=1` and every `u,w∈ℕ`, there exist `W,n,a,b∈ℕ` such that

```text
W ≡ w (mod m),
BB429.run n (u,W) = some (a,b),
BB429.next (a,b) = none.
```

One may moreover require `W≥w`. This extends Agent 4's [all-dyadic-cylinder result](../agent4-bb429-dyadic-barrier/README.md) from powers of two to **every modulus not divisible by three**, including odd prime powers and mixed composite moduli.

**Stronger corollary.** Fix such an `m`. No nonempty predicate `P(u,w)` that (i) is saturated under `w ≡ W (mod m)` **for each fixed exact first coordinate `u`**, (ii) is forward invariant under every successful full-source `BB429.next` transition, and (iii) excludes every halting state, can exist. From any `P(u,w)`, choose the synthetically halting `(u,W)` with the **same exact `u`**. Saturation implies `P(u,W)`; induction along its finite real accelerated trace implies `P(a,b)`, contradicting (iii). In particular, the result rules out every fixed-modulus two-counter invariant, while allowing `P` to depend arbitrarily on the unbounded exact first counter. This strengthens the prior dyadic barrier at both modulus and predicate levels.

## Complete arithmetic argument

Fix arbitrary `A∈ℕ`. Define the **integer** sequence `F_A(n)=A·2^n−3n`. We first prove a stand-alone congruence-surjectivity lemma:

> For every `m≥1` with `gcd(m,3)=1`, every integer target `t`, and every lower bound `L`, there exists `n≥L` such that `F_A(n)≡t (mod m)`.

Use strong induction on `m`. The case `m=1` is immediate. For `m>1`, write `m=2^a q` with `q` odd. If `q=1`, put `p=1`; otherwise put `p=ord_q(2)`, the positive multiplicative order of 2 modulo `q`. The order exists because 2 is invertible modulo odd `q`, and satisfies `1≤p≤φ(q)<q≤m`. Thus always `1≤p<m`, and for every `n≥a`,

```text
2^(n+p) ≡ 2^n (mod m).
```

Indeed, both powers vanish modulo `2^a`; their difference vanishes modulo `q` by the order relation, hence modulo the coprime product `m`.

Set `g=gcd(m,p)`. Then `1≤g<m` and `gcd(m,3p)=g`, since `gcd(m,3)=1`. The induction hypothesis, used with lower bound `max(L,a)`, supplies `n≥max(L,a)` satisfying `F_A(n)≡t (mod g)`. A linear congruence `3pv≡F_A(n)−t (mod m)` consequently has some nonnegative solution `v`, because its right-hand side is divisible by exactly the required gcd `g`. Let `n'=n+pv`. Repeating the power-period identity gives

```text
F_A(n') ≡ F_A(n)−3pv ≡ t (mod m).
```

Also `n'≥L`, completing strong induction. This is a proof for *arbitrary* moduli and targets, without finite modulus sampling.

For the #429 machine, choose `A=4(u+3)`, `t=2u+w+13`, and `L=u+w+2`. Take the resulting `n≥L` and define

```text
W = 4(u+3)·2^n − (2u+3n+13).
```

Since `2^n≥n+1` and `n≥u+w+2`, we have

```text
W ≥ 9n−2u−1 ≥ w.
```

Thus `W` is a natural number, `W≡w (mod m)`, and

```text
2u + W + 3n + 13 = 4(u+3)·2^n.
```

The established [Agent 5 exact first-branch criterion](../agent5-429-rank/BB429Burst.lean), theorem `BB429Burst.burst_gateway_iff`, converts this identity into an actual finite first-branch run ending at `b+1=2a`. Agent 4's `BB429DyadicStarts.first_prefix_is_source` transfers that run to the **complete** `BB429.next/run` map; Agent 5's `BB429.next_none_iff_halt_line` proves termination at the endpoint. These final steps use the source semantics rather than an unverified arithmetic surrogate.

## Why the factor 3 matters

For `u=0`, every direct first-burst halting seed of the displayed exponential form satisfies `W≡−13≡2 (mod 3)`. Hence this particular construction cannot establish surjectivity for moduli divisible by three. This is a limitation of this *first-burst construction*, not a claim that all other residue classes are nonhalting. For example, an independent exact branch simulation shows synthetic `(0,60)` reaches the halting line `(93,185)` after 58 macro steps, although `60≡0 (mod 3)`.

## Executable checks, status, and overlap

[The deterministic BigInt SFT](CoprimeModuliSFT.cjs) implements the induction as an explicit modular witness algorithm: factor out powers of two, compute the order of two modulo the odd factor, solve the smaller-gcd instance recursively, and lift using a modular inverse of `−3p/g`. It independently follows the **entire twelve-branch `next`** from each constructed synthetic start and verifies every intermediate step uses the real first branch and that the final state halts. It also checks known blank-root checkpoints. The finite tests corroborate the theorem but are not used as its proof.

**Evidence boundary:** The general all-moduli congruence lemma and its inductive proof above are new handwritten mathematics in this investigation, **not yet Lean-kernel checked**. The source-level first-burst and halting bridge are previously Lean-certified repository results; the SFT reproduces concrete instances against an independent transcription. This method result does not furnish any actual-blank halting witness or nonhalting invariant. It shows that a *purely fixed finite modulus* counter-state forward invariant cannot possibly finish #429's nonhalting proof for any `m` coprime to 3. Invariant constructions with nonperiodic history, root-sensitive reachability, or restrictions to genuine subsection states remain viable.
