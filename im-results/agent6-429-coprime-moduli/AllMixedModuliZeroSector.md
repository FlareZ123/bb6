# All mixed moduli: synthetic BB429 residue-zero sector via a nested-exponential period

**Agent 6, 2026-11-05. Mathematical research intermediate, independent all-parameter Lean formalization pending.** This improves the [three-adic construction](AllThreeAdicCylinders.md): the already source-certified two-burst family with initial second counter divisible by three covers **every multiple-of-three residue modulo every positive modulus**, including arbitrary coprime factors. It is a theorem about *synthetic* initial states, with no claim that the genuine blank orbit reaches any of them. This is not a decision of #429 or BB(6).

## Exact family and theorem

Recall from [Agent6TwoBurstZero.lean](Agent6TwoBurstZero.lean) the original twelve-branch `BB429.next` synthetically halting family, for `c>=2`:
```text
N(c)  = 4*2^c+c-10
H(c)  = 4*2^N(c)-8*2^c+13-c
W0(c) = 3*H(c) = 12*2^N(c)-24*2^c+39-3*c
```
The [original repository accelerator CI 42057234115](https://github.com/FlareZ123/bb6/actions/runs/42057234115) verifies an actual complete-map halting trajectory from `(0,W0(c))` for every `c>=2`, with standard Lean axioms only.

**New mathematical theorem.** For every positive integer `m`, integer target `r`, and lower cutoff `L`, there is `c>=max(2,L)` with
```text
H(c) ≡ r (mod m).
```
Consequently the residues `W0(c) mod m` are exactly the multiples of `gcd(3,m)` modulo `m`. In particular, whenever `3|m`, all residues `r≡0 (mod3)` are covered, without any restriction on the other prime factors of `m`. The starting **first** counter remains exactly zero.

## Two elementary period lemmas

Write `φ` for Euler's totient. For every `v>=1`, every `x` sufficiently large, and every positive multiple `t` of `φ(v)`:
```text
2^(x+t) ≡ 2^x (mod v).
```
This is true even when `v` is even: write `v=2^a z` with `z` odd. For `x>=a`, both powers are zero modulo `2^a`; modulo `z`, Euler's theorem and `φ(z)|φ(v)` give the required period. The `v=1` case is trivial.

For `m>1` set
```text
p = lcm(φ(m),φ(φ(m))).
```
For all sufficiently large `c`, apply the first lemma once with modulus `m`, and once with modulus `φ(m)`. As `φ(m)|p` and `φ(φ(m))|p`, both congruences hold:
```text
2^(c+p) ≡ 2^c (mod m)
2^(c+p) ≡ 2^c (mod φ(m)).
```
The exact exponent identity is
```text
N(c+p)-N(c) = 4*(2^(c+p)-2^c)+p.
```
Thus `N(c+p)≡N(c) (mod φ(m))`, and (for `N(c)` sufficiently large) the first lemma implies
```text
2^N(c+p) ≡ 2^N(c) (mod m).
```
Combining the two power terms with the linear `-c` gives the **uniform eventually valid shift identity**
```text
H(c+p) ≡ H(c)-p (mod m).                     (★)
```
A finite threshold `C(m)` can be taken as `max(2,v₂(m),v₂(φ(m)))`, since `N(c)>=c` for `c>=2`. This statement is for all `c>=C(m)`, with no bound on `m`.

## Why the period cannot absorb the modulus

**Claim:** `g=gcd(m,p)<m` for all `m>1`.

Let `P` be the *largest prime divisor* of `m` and `e=v_P(m)>=1`. In the Euler product
```text
φ(m) = ∏_{\ell^f || m} \ell^(f-1)*(\ell-1),
```
every prime divisor of any factor `\ell-1` is less than `\ell<=P`. Hence the exponent of `P` in `φ(m)` is **exactly `e-1`**. The same reasoning applied to `φ(m)`, whose prime divisors are all at most `P`, gives `v_P(φ(φ(m)))<=max(e-2,0)`. Thus
```text
v_P(p) = max(v_P(φ(m)),v_P(φ(φ(m)))) = e-1 < e,
```
so `m∤p`, and therefore `gcd(m,p)<m`. This argument includes prime powers and even moduli.

## Strong induction for surjectivity

Induct on `m`. The assertion modulo one is trivial: choose any sufficiently large `c`. For `m>1`, let `p` and `g` be as above, so `1<=g<m`. By the induction hypothesis, for any target `r` and any sufficiently large cutoff, choose `c>=max(L,C(m))` with `H(c)≡r (mod g)`. The linear congruence
```text
p*v ≡ H(c)-r (mod m)
```
has a nonnegative integer solution `v`, because its solvability criterion is precisely `gcd(m,p)|H(c)-r`. Applying (★) repeatedly for `c,c+p,...,c+(v-1)p` yields
```text
H(c+v*p) ≡ H(c)-v*p ≡ r (mod m).
```
The new index is at least `L`, proving the assertion for `m`. The induction is on a strictly smaller modulus, with no finite-sampling inference.

Finally, for any `r` with `gcd(3,m)|r`, the congruence `3x≡r (mod m)` has a solution `x`; apply the just-proved surjectivity of `H` to this `x`, giving `W0(c)=3H(c)≡r (mod m)`. Conversely, `W0` is always a multiple of 3, so no other residues are possible.

## Scope and checks

This argument reuses classical Euler totient periodicity, standard linear-congruence solvability and elementary largest-prime-factor valuation. Its mathematical priority relative to general modular-surjectivity literature has not been established. It is a **paper theorem**, with representative exact modular computations corroborating the shift, and the parametric underlying halting family independently verified against unaltered source in Lean. It does **not** imply that a fixed-modulus invariant is impossible at all moduli without likewise covering the other starting residues (especially even `1 mod3`), and it does not affect original blank-root reachability.

A natural next formal check is to construct a reusable totient-period lemma in Lean against a known theorem library, then compose it with the source-certified `Agent6TwoBurstZero.full_source_synthetic_halt`. For deciding #429, a substantially higher-value dependency remains a **genuine blank-root post-reset ancestor invariant** that excludes all remaining halting gateways, or a witnessed genuine halt.
