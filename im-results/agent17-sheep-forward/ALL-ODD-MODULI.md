# Every odd-modulus Sheep even-return quotient is a complete directed graph

**Status: intermediate mathematically proved method limitation, November 3, 2026.** The all-odd-modulus extension has a fully quantified elementary written proof, a deterministic implementation of that proof, and 11,500 exact modular tests. The special `3^k` case has additionally been kernel-checked in `ForwardSurj.lean`; the **all-odd prime-by-prime induction is not yet Lean formalized**, and original-machine reduction is reused from Agent16's already successful source CI. This does not decide a BB(6) holdout or establish blank-orbit visits to synthetic states. Original programme R010, [3-adic detailed proof](README.md).

## Theorem

Let `m` be **any positive odd integer**, `m>1`. For every `0≤r,s<m` and every bound `N`, there exist arbitrarily large legal nonterminal even Sheep section states `x≥N` such that `x≡r (mod m)` and their **genuine first even return** `E(x)≡s (mod m)`.

Moreover, the witness can be chosen `x=4^B u`, with `B≥1` and `u≥5` odd satisfying `u≡1 (mod 4)`. Thus `v₂(x)=2B`, the authentic generic return branch is taken, its first successor is already even, and `E(x)=F(x)=x+2B+(u−1)/2`. No exceptional branch or synthetic transition definition is used.

This removes even the possibility of a *proper* modulo-`m` residue-only inductive predicate on the full domain of even section inputs, for every **odd** modulus `m`. It leaves room for information from powers of 2, unbounded histories, correlations, or genuinely blank-reachable sets.

## Arithmetic lemma: all-odd modular solvability

For natural `r,c,b` write

`P(r,c,b)=4^b(4b+c)+r`.

For **every odd positive** `m` and every `r,c≥0`, the congruence

`P(r,c,b)≡0 (mod m)`

has a solution `b≥0`.

**Proof with explicit prime-power induction.**

Factor `m=∏p_i^{a_i}` over odd primes, in **strictly increasing order**. Build a nonnegative exponent `b` and a partial modulus `M=∏_{i<t}p_i^{a_i}` for which `P(r,c,b)≡0 (mod M)`. Initially `M=1`, so any `b` works, e.g. zero.

For a positive odd `M`, let `d_M` be the multiplicative order of `4` modulo `M`; put `d_1=1` and `T=M d_M`. For every `b`,

`P(r,c,b+T)≡P(r,c,b) (mod M)`,

since `M|T` and `4^T≡1 (mod M)`.

Now add the next prime power `p^a`. All prime divisors of `M` are strictly smaller than `p`. By Lagrange's theorem `d_M|φ(M)`, and the prime factors of `φ(M)=∏_{ℓ^e ||M}ℓ^{e−1}(ℓ−1)` are also strictly smaller than `p`. Therefore **`p∤T`**. Let `d=ord_p(4)`, which divides `p−1`; thus `p∤Td`.

For `j=0,1,…,a−1` suppose we have achieved `P(r,c,b)≡0 (mod p^j)` while preserving the previous condition modulo `M`. Set

`L_j=T d p^j`.

Because `4^d≡1 (mod p)` and `p` is odd, standard binomial lifting of `(1+ph)^{p^j}` proves

`4^{L_j}≡1 (mod p^{j+1})`.

Consequently, for every natural `t`,

`P(r,c,b+tL_j)≡P(r,c,b)+4^{b+1}T d·t·p^j (mod p^{j+1})`.

The coefficient `4^{b+1}Td` is invertible modulo `p`. Since the current `P(r,c,b)` is divisible by `p^j`, **exactly one** choice of `t modulo p` makes the right side divisible by `p^{j+1}`. Choose its representative `0≤t<p` and replace `b` by `b+tL_j`. Because `T|L_j`, the older condition modulo `M` remains true. Repeating through `j=a−1` yields a root modulo `Mp^a`. The new `M` is the enlarged partial product, so induction reaches the full `m`. QED.

The increasing-prime order is essential to the simple `p∤T` argument. Processing primes in an arbitrary order may make this particular lifting step degenerate. The proof is constructive and requires no unverified heuristic about orbit density.

## Lifting a modular root to a genuine Sheep edge

Choose `c=2r+2m−2s−1>0`, and let `b` be the lemma's solution. Let `D=ord_m(4)`, `T_m=mD`, and `B=b+T_m≥1`. The root survives because `4^{T_m}≡1 (mod m)` and `m|T_m`:

`4^B(4B+c)+r≡0 (mod m)`.

Since `m` is odd, use the Chinese remainder theorem to choose arbitrarily large `u≥5` with

`u≡r·4^(−B) (mod m)`, `u≡1 (mod 4)`.

All inverse powers exist modulo `m` because `4` is coprime to `m`. Set `x=4^B u`. Then `x≡r (mod m)`, `E(x)=F(x)=x+2B+(u−1)/2` is even, and the root congruence, multiplied by `4^(−B)`, gives

`4B+c+u≡0 (mod m)`.

Thus

`2E(x)≡2r+4B+u−1≡2r−c−1≡2s (mod m)`.

Cancellation of 2 is valid because `m` is odd, proving `E(x)≡s`. Sending `u` to infinity through the CRT arithmetic progression keeps the congruences and legality unchanged. QED.

## Reproducible exact implementation

[`general_odd.py`](general_odd.py) implements the proof: factorization in increasing prime order, exact multiplicative orders, the prime-digit shift `L_j=T·ord_p(4)·p^j`, exhaustive choice of the unique `t∈{0,…,p−1}` at each lift, and exact CRT construction of a genuine generic Sheep edge. It asserts every intermediate modular condition and directly computes the true `F(x)` when the constructed bit length is moderate. No random decision affects the proof procedure; pseudorandom pairs only select additional test cases.

Deterministic Python 3 results:

```text
PASS odd q<=201, all r, one sampled s per r: 10200
PASS larger odd q, seeded samples: 11500
```

The first run covers all 100 odd moduli `3,…,201`, all their source residues `r`, and one deterministic target residue each (10,200 pairs); the second includes 100 pairs each for `243,245,315,343,375,405,441,625,729,945,1001,1331,3125` (1,300 more). The earlier independent `3^k` checker exhausts all pairs through `3^4`. No finite test is claimed to prove the universal theorem; the written induction supplies the universal argument.

## Consequences, limitations and prior work

A forward invariant asserting only that the current even section value lies in a fixed **proper** set of odd-modulus residue classes cannot be inductively closed over the full legal even-return relation while containing the authentic starting value `10`. Every included source residue has a genuine one-step edge to every excluded target residue, from arbitrarily large synthetic inputs.

The theorem **does not show any of these synthetic source states occur on the blank-start trajectory**, and is compatible with an invariant using a finer state than one fixed odd modulus. The particular promise of the pilot was to test whether a 3-adic residue automaton could resolve the true orbit; the result establishes a much broader obstruction to that restricted class of proof methods.

This general theorem has not received independent peer review, Lean formalization of the prime-factor induction, or exhaustive external-prior-art assessment. The closest in-repository antecedents are Agent16's exact source-connected even-return map, Agent39's source-verified power-of-three lifting and inverse odd blocks, and Agent17's prior bounded symbolic inverse trees. The result belongs in intermediate research until its utility and originality are independently assessed.
