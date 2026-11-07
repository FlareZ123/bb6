# Surjectivity of the valuation-forgotten affine transition modulo odd moduli

**Status:** rigorous paper proof; not yet formalized in Lean. This is a limitation on a coarse modular abstraction. It is not a statement that the actual blank-start orbit reaches every residue.

## The affine relaxation

For an actual high-level transition from counter `d), write `d+2=2^v(2q+3)`. The update is

`d' = d+v+3(q+1)`.

Fix an odd modulus `M). Since 2 is invertible modulo M, let `u=2^{-1}∈(ℤ/Mℤ)ˣ`. The transition identity can be rewritten modulo M as

`d' ≡ d+v-3u+3(d+2)u^(v+1) (mod M)`.

For fixed `M,d`, define the relaxed affine image

`F(v) = d+v-3u+3(d+2)u^(v+1) ∈ ℤ/Mℤ`.

For an actual transition, the chosen v is constrained by `v=ν₂(d+2)`. In this relaxation, v is allowed to range freely over all natural numbers.

## Theorem

For every odd `M≥1`, every residue `d∈ℤ/Mℤ`, and every target residue `r∈ℤ/Mℤ`, there exists `v≥0` such that

`F(v)=r`.

Thus, after forgetting the coupling between the counter and its true 2-adic valuation, the one-step affine family from any state is surjective modulo every odd modulus.

## Proof

Proceed by strong induction on odd `M`. The case `M=1` is immediate.

Let `M>1`, and let `L` be the multiplicative order of `u` modulo M. Then `1≤L<M`. To see the strict bound, the M powers `1,u,…,u^(M-1)` are all units. There are at most M−1 nonzero residue classes modulo M, so two powers coincide. Cancelling the smaller power gives a positive period at most M−1. Minimality of L gives the bound.

Since `u^L=1`, for every v,

`F(v+L)=F(v)+L (mod M)`.

Put `g=gcd(L,M)`. Then `g≤L<M`, and g is odd. Reduce the same formula modulo g. Because `g∣L` and `u^L=1pmod g`, the function modulo g is L-periodic:

`F_g(v+L)=F_g(v)`.

By the induction hypothesis, there is some v with `F_g(v)=rpmod g`. Reduce v modulo L using L-periodicity, obtaining `0≤v₀<L` with `F_g(v₀)=rpmod g`.

Now consider `v=v₀+jL`. Repeated use of the shift identity gives

`F_M(v₀+jL)=F_M(v₀)+jL (mod M)`.

The residues `jLpmod M` are exactly the multiples of g modulo M. Since `F_M(v₀)equiv rpmod g`, the difference `r-F_M(v₀)` is such a multiple. Choose j to obtain `F_M(v₀+jL)=rpmod M`. This completes the induction.

## Consequence for BB(6) research

A proof strategy that tracks only `d mod M` for a fixed odd M, while allowing the valuation input v to vary independently, cannot produce a nontrivial invariant set: the relaxed one-step image is already every residue. A useful modular invariant must retain additional information about the true coupling `v=ν₂(d+2)`, such as a sufficiently rich 2-adic history or a stronger state representation.

This does **not** rule out modular proofs for the actual machine. The relaxation discards precisely the valuation constraint that defines the real transition. It only explains why searches over unconstrained odd-modulus residue graphs are too coarse.

A small Python check also found full relaxed images for every odd modulus through 101 and every starting residue; the induction proof above is independent of that finite check.
