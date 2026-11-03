# A universal high-2-adic zero-fiber edge theorem for Sheep's even return

**Status:** an elementary constructive paper theorem, intermediate research. It extends the all-odd-modulus proof in [ALL-ODD-MODULI.md](ALL-ODD-MODULI.md) by a constrained root construction. The new constrained-root lemma is **not yet Lean kernel formalized**; its `H=1,m=3^k` special case is checked in [ForwardSurj.lean](ForwardSurj.lean). This result does not establish actual blank-tape reachability of its synthetic sources or decide any BB(6) machine.

## Theorem (the zero 2-adic fiber hits every even residue)

Let `m=2^k n` with `k≥1` and `n≥1` odd. Let source residue `r` modulo `m` satisfy `r≡0 (mod 2^k)`; let target residue `s` modulo `m` satisfy `s≡0 (mod 2)`. For every bound `N` there exists a legal nonterminal even Sheep section input `x≥N` such that

`x≡r (mod m),   E(x)≡s (mod m)`,

where `E` is the genuine **first-even** return of the original section map. The witness can be chosen `x=4^B u` with `u≥5` and `u≡1 (mod4)`, so `E(x)=F(x)=x+2B+(u−1)/2`.

In particular, for any modulus `m`, **once a globally inductive residue-only predicate on even section inputs includes one residue divisible by the largest power of two dividing `m`, it must include every even residue modulo `m`**. When `m` is odd, all residues already have one-step complete connectivity by [the general odd-modulus theorem](ALL-ODD-MODULI.md). The remaining obstacle to disproving *all* finite-modulus residue-only proofs is showing that any proper closed abstract set containing the actual initial residue 10 must enter the zero 2-adic fiber. This is a mathematical question about the quotient graph; it does **not** imply a real blank orbit ever hits that fiber.

## Lemma: modular roots with a prescribed coprime stride

For every odd positive `n`, every natural `r,c`, and every positive natural `H` with `gcd(H,n)=1`, there exists `b≥0` divisible by `H` such that

`P(r,c,b)=4^b(4b+c)+r ≡0 (mod n)`.

**Proof.** Repeat the increasing-prime induction in [the all-odd proof](ALL-ODD-MODULI.md). Start from `b=0` modulo the empty product `M=1`. For each new odd prime power `p^a`, define the old period `T=H·M·ord_M(4)`. Because `p∤H`, all primes in `M` are smaller than `p`, and `ord_M(4)|φ(M)`, we have `p∤T`. For each `j=0,…,a−1`, shift `b` by an appropriate multiple `tL_j`, where

`L_j=T·ord_p(4)·p^j`, `0≤t<p`.

As before, `4^{L_j}≡1 (mod p^{j+1})`, and

`P(r,c,b+tL_j)≡P(r,c,b)+4^{b+1}T·ord_p(4)·t·p^j (mod p^{j+1})`.

The unit coefficient modulo `p` permits a unique lift to the next p-adic digit. Because each `L_j` is a multiple of both `H` and the old period `M·ord_M(4)`, every shift preserves `H|b` and the preceding congruences modulo `M`. Induction solves the full modulus `n`. QED.

## Exact edge construction

Let `r_0=r mod n`, `s_0=s mod n`, and `s_2=s mod 2^k`, with `s_2` even. Put `H=2^{k−1}` and `c=2r_0+2n−2s_0−1>0`. Apply the constrained-root lemma to obtain `H|b` and `P(r_0,c,b)≡0 mod n`. Let

`B=b+H·n·ord_n(4)`,

taking `ord_1(4)=1`; this positive shift is a period of `P` modulo `n`, preserves the root, and is divisible by `H`. Since `B≥H=2^{k−1}`, we have `2B≥k` and `2^k|2B`.

By CRT for the coprime moduli `n` and `2^{k+1}`, choose arbitrarily large `u≥5` with

`u≡r_0·4^(−B) (mod n)`, and `u≡1+2s_2 (mod 2^{k+1})`.

The second congruence implies `u≡1 (mod4)` because `s_2` is even. Hence `x=4^B u` is legal and sufficiently large. Since `2B≥k`, `x≡0 (mod 2^k)`, and the first congruence makes `x≡r_0 (mod n)`; together these imply `x≡r (mod m)`.

The genuine generic first successor is even, and modulo `2^k` it satisfies

`E(x)=x+2B+(u−1)/2≡s_2 (mod2^k)`,

because `2^k|x`, `2^k|2B`, and `u≡1+2s_2 (mod2^{k+1})`. The modular root argument from the all-odd proof simultaneously gives `E(x)≡s_0 (mod n)`. CRT combines these into `E(x)≡s (mod m)`. Raising `u` by multiples of `n2^{k+1}` preserves every condition and makes the source arbitrarily large. QED.

## Reproduction and limits

[zero_fiber.py](zero_fiber.py) is a deterministic standard-library-only exact checker. It implements the independent stride-constrained prime-by-prime solver and the source/target CRT conditions. It verifies **6,240 constructed edges** over all `k=1,…,8`, odd `n=1,3,…,51`, and 30 seeded source/target residue samples per pair, including direct construction of the integer `x` and `E(x)` whenever a witness size is moderate:

```
PASS 2-adic zero-fiber 1 cases 780
PASS 2-adic zero-fiber 2 cases 1560
...
PASS 2-adic zero-fiber 8 cases 6240
COMPLETE 6240
```

This exact finite test cannot certify the universal lemma; the written prime-power induction supplies that proof. Neither the general all-odd theorem nor this conditional zero-fiber theorem proves that any synthetic source comes from the true blank start `5→7→10`. The original machine halting question and BB(6) remain unsettled. Only the power-of-three lifting lemma is currently kernel certified; the additional stride reasoning is elementary but awaits separate formalization and independent review.
