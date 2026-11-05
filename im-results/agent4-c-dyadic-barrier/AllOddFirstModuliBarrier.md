# Machine C: all odd first counters admit synthetic stopping inputs in right residue 1 modulo every modulus

**Agent 4, 2026-11-05. Intermediate arithmetic theorem; no genuine-blank halting or BB(6) decision.** This extends [AllFiniteModuliBarrier.md](AllFiniteModuliBarrier.md), which fixed the first counter at 5, to *every* positive odd first counter. The argument is a mathematical paper proof using the already original-source-certified Machine C stopping equation. The new unrestricted quantifiers have not been formalized in Lean.

## Statement

For every `u : Nat` and positive integer `M`, there is `K : Nat` such that

```text
K ≡ 1 (mod M)
BB6.Agent46.secNext (2*u+1,K) = none.
```

In fact an arbitrarily large natural stopping-index `n≥1` can be chosen. Define
```text
F_u(n) = (u+2)*(4^n-1)-3*n,
K = F_u(n)+1.
```
The existing exact Machine C source stopping criterion (`Agent1Unified.source_section_halts_iff_one_equation`) yields `secNext(2u+1,K)=none` whenever `K+u+3m+4=4^(m+1)*(u+2)`. This is an identity for `m=n-1`; moreover `K≥1` for every `n≥1`. It suffices to construct `n≥1` with `M | F_u(n)`.

## Constructive arithmetic proof

Factor `M=2^e 3^j ∏ p_i^a_i`, with `5≤p_1<...<p_t`. By CRT choose arbitrarily large `n` satisfying
```text
3*n ≡ -(u+2) (mod 2^e)
n ≡ 0 (mod 3^j)
n ≥ max(1,e).
```
The first congruence exists because 3 is invertible modulo `2^e`; the two moduli are coprime. For `n≥e`, `4^n≡0 (mod 2^e)`, so `F_u(n)≡-3n-(u+2)≡0`. Since `4^(3^j)≡1 (mod 3^j)`, the second congruence gives `4^n≡1 (mod 3^j)` and `3n≡0`. Thus `M_0=2^e 3^j` divides `F_u(n)`.

Suppose inductively that `M_0=2^e B | F_u(n)`, with `B` odd and all prime factors of `B` smaller than the next prime `p≥5`. Set
```text
R = M_0 * phi(B) * ord_p(4).
```
All factors of `R` have prime factors smaller than `p` (use the totient product formula and `ord_p(4) | p-1`), so `p∤R`. Also `M_0|R`, `4^R≡1 (mod B)` by Euler's theorem, and `4^R≡1 (mod p)` by definition of the order. Binomial lifting gives `4^(R*p^k)≡1 (mod p^(k+1))` for every `k≥0`.

If `p^k|F_u(n)`, put `T=R*p^k`. For any `z≥0`,
```text
F_u(n+T*z) ≡ F_u(n)-3*T*z (mod p^(k+1)).
```
Since `p∤3R`, choose `z∈{0,...,p-1}` to cancel the next p-adic digit, yielding `p^(k+1)|F_u(n+Tz)`. The old modulus `M_0` remains a divisor: the linear term shifts by a multiple of `M_0`; the exponential term has period `T` modulo odd `B`; both `4^n` terms vanish modulo `2^e`. Iterate `a_i` times, adjoin `p_i^{a_i}`, and continue in increasing prime order. After finitely many stages `M|F_u(n)`.

The output `n` can be chosen beyond any prescribed threshold by increasing the initial CRT solution, so the construction produces arbitrarily large stopping inputs. This proof works uniformly for `u` and `M`.

## Consequence and evidence limits

For a *fixed exact odd first counter* `a=2u+1`, no halt-excluding predicate `P(a,k)` can simultaneously include `P(a,1)`, be saturated under congruence of the right counter modulo a fixed `M`, and exclude every immediately stopping input. In particular `a=5` recovers the previous blank-section congruence obstruction. The argument makes **no assertion that any synthetic stopping input lies on the actual blank orbit**. It does not rule out reachability proofs carrying ancestry or noncongruential information.

The earlier all-modulus proof gave the `a=5` case. This note makes the first-coordinate quantifier explicit. It is a structural strengthening of a method limitation, with no claim of external mathematical novelty or improved BB(6) bound. The companion [verify_odd_left_all_moduli.py](verify_odd_left_all_moduli.py) independently constructs modular witnesses, checks every intermediate lift, and source-interprets small examples. Computational tests corroborate the proof and are not substituted for it.


## Shorter uniform proof: totient-period strong induction without prime-power lifting

The prime-by-prime construction above can be replaced by a shorter proof, and this version is preferable for a future all-parameter Lean formalization. It avoids a prime-power ordering, discrete multiplicative orders and binomial lifting. The statement also holds at the arithmetic level for *any* coefficient `A≥0` in `F_A(n)=A(4^n-1)-3n`; the Machine C specialization is `A=u+2`.

Put `B=2^e 3^j`, `q=M/B`; thus `gcd(q,6)=1`. Fix `A` and a lower bound `L`. Choose an arbitrarily large base index `n_0≥max(L,e,1)` satisfying `3n_0≡-A (mod2^e)` and `n_0≡0 (mod3^j)`, as before. Every index `n=n_0+B t` (`t≥0`) satisfies `B|F_A(n)` by exactly the same base argument.

Prove by **strong induction on `q≥1`**, with fixed `A,B,n_0`, that there exists `n=n_0+Bt` satisfying `q|F_A(n)`. When `q=1` take `n_0`. When `q>1`, let `h=φ(q)` and `g=gcd(q,h)`. Euler's theorem applies because `q` is odd: `4^h≡1 (modq)`. Since `1≤h<q`, we have `1≤g<q`; also `gcd(g,6)=1`, so the induction applies to `g`. It supplies an index `n=n_0+Bt` with `g|F_A(n)`.

Put `R=B h`. Then `4^R≡1 (modq)` by Euler, and
```text
F_A(n+R v) ≡ F_A(n)-3 R v (mod q)      for every v≥0.
```
Because `gcd(q,3R)=gcd(q,h)=g` (using `gcd(q,6B)=1`), the ordinary linear-congruence theorem gives a `v≥0` with `3R v≡F_A(n) (modq)`. The new `n'=n+Rv=n_0+B(t+hv)` stays in the base progression, keeps `B|F_A(n')`, and satisfies `q|F_A(n')`. Since `gcd(B,q)=1`, `M=Bq|F_A(n')`. This completes the theorem for arbitrary `A,M,L`.

The independent executable recurrence in [verify_odd_left_totient.py](verify_odd_left_totient.py) uses precisely the smaller-`g` recursion, with no prime-power lifting. It passed 43,000 parameter pairs in an initial independent local check. A formal proof may replace Euler's totient by **any** positive period `h<q` of `4^n (modq)`, allowing a finite pigeonhole argument instead of constructing totients.

This short proof is mathematically equivalent in final scope to the longer prime-lifting proof above; it improves conceptual economy and machine-checking prospects rather than changing BB(6)'s unresolved root questions.
