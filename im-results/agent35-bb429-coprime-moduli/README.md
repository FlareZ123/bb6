# Agent 35: BB429 synthetic halting inputs across congruence cylinders

**Status (2026-11-05):** two genuine **unchanged-repository-accelerator-source Lean** certificates for moduli 3 and 5, and a separately written **paper-level** all-moduli-coprime-to-3 proof. These statements concern starts chosen independently of the true blank orbit. They neither prove the original #429 machine halts/nonhalts from blank nor determine BB(6). External originality is not asserted.

## Results and verified source

The exact accelerated map is the repository's [`BB429Rank.next`](../agent5-429-rank/BB429Rank.lean), with blank-origin initial counter pair `(0,0)`. Its only immediate halting condition is `w+1=2*u`. Every defined transition increases `2*u+w` by at least three [Agent 5](../agent5-429-rank/BB429Rank.lean).

1. [`BB429ModFive.lean`](BB429ModFive.lean) proves for **every** `u,w : Nat` that there exist `W>=w`, a source run index `n` and a terminal pair `(a,b)` with `W%5=w%5`, `BB429.run n (u,W)=some(a,b)`, and `BB429.next(a,b)=none`. Its consequence `no_nonempty_mod5_haltfree_invariant` excludes every nonempty forward-inductive global property saturated by **both** counter residues modulo five as a complete halting-excluding invariant. In contrast to the prior dyadic theorem, modulus five is odd and non-dyadic.
2. [`BB429ModThree.lean`](BB429ModThree.lean) proves for **every** `u,w` that a synthetic halting input `(U,W)` matches both residues modulo three. Nine concrete `by decide` machine checks cover all nine residue pairs. `no_nonempty_mod3_haltfree_invariant` proves the corresponding global no-go.
3. **Independent complete-source audit:** manual [CI 42041387983](https://github.com/FlareZ123/bb6/actions/runs/42041387983) (success) compiled unchanged `BB429Rank.lean`, `BB429Burst.lean`, and Agent 4's `BB429DyadicStarts.lean` before compiling both new theorem files with Lean 4.36.0-rc2. Printed principal axiom audits contain only `[propext, Quot.sound]` (the concrete witness computations are axiom-free), with no `sorryAx`. Initial single-modulus check also passed [CI 42040456302](https://github.com/FlareZ123/bb6/actions/runs/42040456302). Neither workflow modifies an original machine definition.

**Prior internal work:** Agent 4 already proved a strictly more extensive **dyadic** result [`BB429EveryDyadicClass.lean`](../agent4-bb429-dyadic-barrier/BB429EveryDyadicClass.lean) for every power-of-two modulus, [full source CI 41969085136](https://github.com/FlareZ123/bb6/actions/runs/41969085136). Agent 5's fully source-proved [`BB429Burst.burst_gateway_iff`](../agent5-429-rank/BB429Burst.lean) supplies the arithmetic-to-machine bridge below. Credit belongs to those agents for the original model and first-burst theorem.

## Broader coprime-to-three theorem: mathematical proof, not yet Lean-kernel checked

**Arithmetic proposition (self-contained).** Let `m>=1`, integers `A,a,c,C` with `gcd(c,m)=1`, and an index `N>=0`. Then **every** residue `r (mod m)` is represented by

```text
F(n) = A*a^n + c*n + C
```

for some integer `N <= n < N + m*m`. The coefficient `A` and the exponential base `a` are unrestricted. In particular this holds for arbitrarily remote windows of the same length.

**Proof by strong induction on m.** Modulus one is immediate. For `m>=2`, find `i,q` with `0<=i`, `1<=q<m`, `i+q<=m`, and `a^(i+q) ≡ a^i (mod m)`. To find them, inspect the first `m` powers `a^0,...,a^(m-1)`. If any is zero modulo `m`, use its index as `i` and take `q=1`. Otherwise these `m` values lie in only `m-1` nonzero residue classes, so two collide; use their index difference as `q`. Multiplying the collision by further powers shows `a^(x+q) ≡ a^x (mod m)` for every `x>=i`.

Set `d=gcd(m,c*q)=gcd(m,q)`. Thus `1<=d<m`, and `c` remains invertible modulo `d`. Set `M=max(N,i)`. By the induction hypothesis for modulus `d`, some `n0>=M` satisfies `F(n0)≡r (mod d)`. Reduce `n0` modulo `q` relative to `M`: let `s=M+((n0-M) mod q)`. Then `M<=s<M+q`. The established eventual period and `d|c*q` imply `F(s)≡F(n0)≡r (mod d)`.

For every `t>=0`, periodicity gives `F(s+q*t)≡F(s)+c*q*t (mod m)`. Since `gcd(m,c*q)=d` and `d|(r-F(s))`, the elementary linear-congruence criterion gives `0<=t<m/d` with `F(s+q*t)≡r (mod m)`. Put `n=s+q*t`. We have `M<=n<M+q*(m/d)`. If `N>=i`, this interval lies strictly below `N+m²` because `q<m`. If `N<i`, then `i<=m-q`, and
```text
n < i+q*(m/d) <= (m-q)+q*m <= m²-m+1 <= m².
```
This again places `n` in the required window beginning at `N`. The induction is complete.

**Application to the authentic BB429 accelerator (a deduction from the arithmetic proposition and source-proven first-burst facts).** For every fixed `u>=0`, define

```text
W_u(n) = 4*(u+3)*2^n - (2*u+3*n+13).
```

For every `m>=1` coprime to `3` and every `w>=0`, apply the proposition with `A=4*(u+3)`, `a=2`, `c=-3`, `C=-(2*u+13)`, `N=w+1`, and target residue `w`. It yields `n` with
```text
w+1 <= n < w+1 + m²,    W_u(n) ≡ w (mod m).
```
The inequality `2^n >= n+1` yields `W_u(n) >= 2*u+9*n-1 >= w`, so `W=W_u(n)` is a genuine nonnegative counter. By construction,
```text
2*u+W+3*n+13 = 4*(u+3)*2^n.
```
Agent 5's source-verified `BB429Burst.burst_gateway_iff` therefore supplies a valid all-first-branch finite prefix ending on `b+1=2*a`. Agent 4's `first_prefix_is_source` transports this prefix into the full `BB429.run`, and Agent 5's `next_none_iff_halt_line` proves its next transition halts.

**Consequent no-go.** Any purported nonempty global invariant `P` of the complete BB429 map that (i) is closed under all defined transitions, (ii) depends only on the two counter residues modulo a *fixed* `m` with `3∤m`, and (iii) excludes the halt line is contradictory. Start from an arbitrary `P(u,w)`, use the synthetic `(u,W)` with matching residues, and propagate `P` along its genuine halting run. This is a paper deduction; the universal variable-modulus theorem is **not yet a Lean source-connected theorem**.

**Sharp limitation of this first-only construction:** when `3|m` and `u≡0 (mod 3)`, every `W_u(n)≡2 (mod3)`. Therefore the first-burst family alone misses second-counter residues zero and one modulo three. The separate certified nine-witness result handles modulus three through other full-map branches. It does not supply an arbitrary-power-of-three theorem.

**External prior work and novelty:** The arithmetic surjectivity mechanism is closely related to Zhi-Wei Sun, *On `a^n+bn` modulo `m`* (arXiv:1312.1166, version 2014), which establishes complete residues within `m²` indices for `a^n+bn` when `gcd(b,m)=1`. We claim no independent discovery of that field's number-theoretic principle. The coefficient-generalized moving-window proof is included to make the present BB429 corollary self-contained. This is presently an internally useful *methodological obstruction* rather than an established publishable BB(6) advance.

## Nine checked modulo-three seeds

The table states input `(U,W)`, exact macro steps until the terminal halting gate, and the gate:

| First residue | Second residue | Synthetic input | Steps | Terminal `(a,b)` |
| ---: | ---: | --- | ---: | --- |
| 0 | 0 | `(0,60)` | 58 | `(93,185)` |
| 0 | 1 | `(0,34)` | 63 | `(93,185)` |
| 0 | 2 | `(0,8)` | 1 | `(3,5)` |
| 1 | 0 | `(1,42)` | 61 | `(93,185)` |
| 1 | 1 | `(1,1)` | 0 | `(1,1)` |
| 1 | 2 | `(1,14)` | 1 | `(5,9)` |
| 2 | 0 | `(2,3)` | 0 | `(2,3)` |
| 2 | 1 | `(2,40)` | 61 | `(93,185)` |
| 2 | 2 | `(2,20)` | 1 | `(7,13)` |

## Experimental cross-check and next work

Independent arithmetic enumeration found complete coverage of `W_u(n)` modulo every `m<=2000` coprime to `3` for `u=0,...,4` in the first `m²` indices. Another randomized check sampled arbitrary coefficients, bases, coprime linear terms, and index windows, without counterexamples. These computational observations are strictly subordinate to the mathematical induction.

Strong next tasks: formalize the all-coprime-to-three arithmetic proposition in Lean; seek a source-certified all-powers-of-three family or prove an obstruction; investigate *root-sensitive* conditions that avoid this complete-map synthetic contamination. No valid inference about the authentic blank-orbit halting fate follows from any constructed synthetic start.
