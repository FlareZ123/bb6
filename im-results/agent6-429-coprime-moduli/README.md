# Machine #429: synthetic halting is dense modulo every modulus coprime to 3

**Agent 6, 2026-11-05. Research intermediate.** This is a mathematical limitation on finite-congruence forward invariants. It concerns *synthetic* initial accelerated states of the same exact machine, not new blank-reachable states. Neither #429 nor BB(6) has been decided. Independent external novelty and a Lean formalization of the new number-theory lemma are pending.

## External mathematical prior art (added after source search)

Zhi-Wei Sun, **“On `a^n+bn` modulo `m`,”** arXiv:1312.1166v3 (27 February 2014), [abstract](https://arxiv.org/abs/1312.1166), [PDF](https://arxiv.org/pdf/1312.1166), proves in Theorem 1.1 that for every integer exponential base `a`, positive modulus `m`, and `gcd(b,m)=1`, the residues `a^n+bn` for `1≤n≤m²` are exhaustive. **This is a clear pre-existing general modular-surjectivity mechanism**, so the present inductive lemma must not be described as an independent number-theory discovery. The explicit extra exponential coefficient `A`, the arbitrarily large witness index, and the BB429 exact-`u` Turing-accelerator application require a mathematical reduction/comparison beyond the literal statement of Sun's theorem, but the methodological antecedent is strong. The prime-to-3 restriction corresponds to Sun's linear-coefficient coprimality condition for `b=-3`.

In particular, the present proof is an elementary adapted derivation, and the meaningful (still unreviewed) contribution is the application to exact first-burst halting and the stronger global-invariant impossibility. Nothing is claimed about external priority for that application.

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

## Additional all-power-of-three result (new method barrier)

[The uniform all-3-adic-cylinder proof](AllThreeAdicCylinders.md) proves by an elementary three-way congruence-lifting induction that for **every** exponent `E≥1` and residue `w mod 3^E`, there is a genuine complete-source-map **synthetic** halting trajectory beginning at `(0,W)` with `W≡w mod 3^E`. It builds on [two explicit infinite two-burst families](ResidueThreeTwoBurst.md) with initial w≡0 and1(mod3), plus the original direct first-burst family w≡2(mod3). Its uniform induction uses the period `2·3^e` of `2^n` modulo `3^(e+1)` and works for arbitrarily high exponents; this is stronger than the 27-case finite Lean table below. The [modular SFT](ThreeAdicLiftSFT.py) covers **every** residue through `3^7` and 100 deterministic targets at each modulus `3^8` to `3^12`.

**Proof-status distinction:** The mathematical derivation is complete on paper and exact finite source-map checks corroborate its two family formulas. The all-parameter theorem has **not yet been Lean-kernel compiled against the original source** and is not a claim about actual blank-root reachability or BB(6). The coprime-to-three theorem remains stronger on the *first-coordinate scope*, since it handles any exact `u`, whereas the all-3-adic theorem currently fixes `u=0`. It leaves mixed moduli with a factor of three and an independent coprime factor undecided as a universal saturation result.

## Additional Lean-checked obstruction at modulus 27 (outside coprime-to-3 range)

The separate source [`BB429Full27.lean`](BB429Full27.lean) proves, for **every** `r<27`, the existence of a concrete synthetic `(0,w)` with `w%27=r` that runs to an actual `BB429.next=none` terminal. Its 27 finite certificates use only 27 exact `BB429.run` reductions, with the longest sample 190 macro steps and largest initial `w=1346`. Thus any forward-invariant, halt-free predicate that includes **some** state with first coordinate `0` cannot be saturated under `w%27` for that fixed exact first coordinate. In particular, no such periodic invariant can include the real blank seed `(0,0)`.

This gives a finite, explicit exclusion of a candidate nonhalting method at `m=27`, which is **divisible by three** and is *not* covered by the new general coprime-to-three induction. The modulo-27 theorem also gives examples for moduli `3` and `9` by reduction, without a claim for all higher powers of three.

**Proof status:** All 27 cases and the resulting universal predicate obstruction compiled locally with Lean **4.36.0-rc2**, importing an exact independently transcribed copy of the checked-in `BB429Rank.next/run` definition. Local `#print axioms` of both final theorems reports `[propext, Quot.sound]`; neither uses `sorry` nor `native_decide`. The checked-in Lean source imports the actual unchanged `BB429Rank`; an end-to-end CI compilation against that original repository module is still outstanding. No pinned external raw Cryptids source was imported in this test. The 27 starts are synthetic and do not give a genuine blank-root halt or a BB(6) bound.

## Why the factor 3 matters

For `u=0`, every direct first-burst halting seed of the displayed exponential form satisfies `W≡−13≡2 (mod 3)`. Hence this particular construction cannot establish surjectivity for moduli divisible by three. This is a limitation of this *first-burst construction*, not a claim that all other residue classes are nonhalting. For example, an independent exact branch simulation shows synthetic `(0,60)` reaches the halting line `(93,185)` after 58 macro steps, although `60≡0 (mod 3)`.

## Executable checks, status, and overlap

[The deterministic BigInt SFT](CoprimeModuliSFT.cjs) implements the induction as an explicit modular witness algorithm: factor out powers of two, compute the order of two modulo the odd factor, solve the smaller-gcd instance recursively, and lift using a modular inverse of `−3p/g`. It independently follows the **entire twelve-branch `next`** from each constructed synthetic start and verifies every intermediate step uses the real first branch and that the final state halts. It also checks known blank-root checkpoints. The finite tests corroborate the theorem but are not used as its proof.

**Evidence boundary:** The general all-moduli congruence lemma and its inductive proof above are a handwritten adaptation of a known broad surjectivity principle (Sun 2014), applied to the machine-specific coefficient, **not yet Lean-kernel checked**. The source-level first-burst and halting bridge are previously Lean-certified repository results; the SFT reproduces concrete instances against an independent transcription. This method result does not furnish any actual-blank halting witness or nonhalting invariant. It shows that a *purely fixed finite modulus* counter-state forward invariant cannot possibly finish #429's nonhalting proof for any `m` coprime to 3. Invariant constructions with nonperiodic history, root-sensitive reachability, or restrictions to genuine subsection states remain viable.
