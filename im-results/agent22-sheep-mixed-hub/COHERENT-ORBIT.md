# Coherent finite Sheep even-return orbits hit every residue class from arbitrarily large starts

**Agent 22 | R010 | 2026-11-03.** This is a stronger consequence of the [dyadic inverse-word theorem](./DYADIC-COMPLETENESS.md) and [all-even-modulus lifting theorem](./MIXED-COMPLETENESS.md). It removes the *changing-representatives-per-edge* weakness of quotient-graph paths. The starting state is still a **chosen arbitrarily large even Sheep section state**, never claimed to equal the authentic blank-origin entry **10**. No BB(6) decision follows.

## Theorem: single-trajectory finite congruence mixing

For every even modulus `m=2^p q`, with `p>=1` and `q>=1` odd, and **every pair** of even residues `r,s (mod m)`, there are **arbitrarily large** positive even integers `x≡r (mod m)` such that the **actual consecutive first-even Sheep returns** from this **single integer x** are all defined, use generic positive section branches, and satisfy

```
E^k(x) ≡ s (mod m),    1 <= k <= floor(p/2)+1.
```

For an odd modulus, choose the unique even representatives modulo `2m`; the same theorem then gives `k=1` for every source and target residue modulo that odd modulus. This is a finite congruence-density result for **selected starts**, with a uniform bound on return count depending only on the 2-adic valuation of the modulus.

The theorem does not assert anything about the eventual orbit of **the exact initial state x=10**. Its strong arithmetic-progression quantifier is essential: the constructed start can be made as large as needed, whereas blank-tape reachability fixes the initial value.

## Proof

### Step 1: lift an inverse word to a *real coherent* finite itinerary

Fix `p` and an even dyadic source residue `r2=r mod 2^p`. By the earlier theorem, `r2` has a unique inverse word

```
W=((a1,h1),...,(aj,hj)),
C=sum_i (ai+hi+1) <= p,
j<=floor(p/2).
```

The word evaluation `Phi_P(W)` makes sense for **every precision `P>=C`** and is compatible under reduction of modulus. Let `P=p+C` and choose an arbitrarily large even integer `x0` with

```
x0 ≡ Phi_P(W)  (mod 2^P),
x0 ≡ r         (mod q).
```

CRT supplies such an `x0` because `q` is odd, and compatibility of the inverse word implies `x0≡r (mod m)`. Taking `x0` sufficiently large ensures that all odd parts encountered in the next finitely many returns are at least 5.

On the generic branch, if `x=2^a u`, `u` odd `>=5`, and `F(x)-1=2^h v` with `v` odd, its exact first-even map is the **affine** function

```
E(x)= (3^h*(1+2^(a+1))*x +
       2^a*(2^(h+1)+3^h*(2a-3))) / 2^(a+h+1).
```

The modular inverse congruence defining `Phi_P(W)` guarantees that, for any sufficiently large integer `x0` in its `2^P` class, the first return has exactly the prescribed pair `(a1,h1)` and the successor lies in the inverse-tail class at precision `P-(a1+h1+1)`. Why exact `h1`? The target tail is even; the inverse relation gives `F(x)-1 = 2^h*(odd)` modulo at least `2^(h+1)` with one extra precision bit since `P>=C+1`. Thus its valuation is exactly `h`. Repeat for the tail. Each step consumes `ai+hi+1` bits of guaranteed precision.

After `j` genuine **consecutive** first-even returns, the result `xj=E^j(x0)` is congruent to the target of the empty inverse word, namely **zero modulo `2^(P-C)=2^p`**. All finite itinerary pairs and all this congruence information are preserved whenever `x0` is shifted by `2^P` times any integer.

### Step 2: exact affine freedom in the final dyadic-zero state

Define

```
alpha = product_i [3^hi * (1+2^(ai+1))].
```

Every factor is odd, so `alpha` is odd. Composing the affine return formulas from Step 1 gives a rational affine map with slope `alpha/2^C` on the entire fixed itinerary cylinder. Let `L=2^(p+C)*q=2^P q`. For every nonnegative integer `t`,

```
x0(t)=x0+L*t,
xj(t)=E^j(x0(t)) = xj(0) + alpha * 2^p * q * t.
```

The initial full residue remains `r`; the itinerary remains the same; the final state is always divisible by `2^p`; and its **odd-modulus residue `xj(t) mod q` is constant**. Denote this last residue by `rho`.

### Step 3: tune the final state's valuation to reach any prescribed target

By the [generalized multiplicative-order descent lemma](./MIXED-COMPLETENESS.md), for **any target** even `s (mod m)` and the fixed `rho`, choose an integer `a>=p` with

```
(2+2^(-a))*rho + 2a-1-2s ≡ 0 (mod q).
```

We want the genuine last state `xj(t)` to satisfy

```
xj(t) ≡ 2^a*(1+2*(s-a))  (mod 2^(a+p+1)).
```

Both sides are divisible by `2^p`. Divide their congruence by `2^p` and use the exact affine formula in Step 2. We obtain the linear congruence

```
alpha*q*t ≡
  [2^a*(1+2*(s-a)) - xj(0)] / 2^p
                              (mod 2^(a+1)).
```

Since `alpha*q` is **odd**, it is invertible modulo `2^(a+1)`. Thus there exists a solution `t`; adding any positive multiple of `2^(a+1)` lets us make the initial state, every intermediate state, and the last state's odd part arbitrarily large.

The chosen congruence forces `xj(t)=2^a u`, where `u` is odd `>=5` and `u≡1+2*(s-a) (mod 2^(p+1))`. Therefore the last generic return

```
F(xj(t))=xj(t)+a+(u-1)/2
```

satisfies `F(xj(t))≡s (mod 2^p)`. Modulo odd `q`, the multiplicative-order congruence from above gives `2F(xj(t))≡2s`, hence `F(xj(t))≡s (mod q)`. Because the target residue is even and the modulus is even, `F(xj(t))` is already even, so **`E(xj(t))=F(xj(t))≡s (mod m)`**. The entire actual finite trajectory from `x0(t)` to this target has length `j+1<=floor(p/2)+1`. All states are arbitrarily large if desired. This completes the proof.

## Exact constructive checks

`verify_coherent_orbit.py` constructs the **single actual starting integer**, checks every prescribed `(a,h)` along its forward orbit, independently replays literal Sheep section returns through odd blocks, validates the final target residue, and checks the length bound. Its first deterministic test implementation passed **107,836 coherent actual source-to-target trajectories** over `p=1,...,7`, `q∈{1,3,5,7,9,11,13,15,21,25,27,31,45}`, all even source residues, and four deterministic target choices per source (deduplicated). Maximum starting state width: 206 bits; maximum even-return length: four. It verifies a genuine forward orbit in each case, while the mathematical proof has no finite parameter bounds.

The CRT and 2-adic inverse formula are consistent with the previously source-verified Sheep semantic reduction (original machine to even-state reachability, successful CI 41505950547). This stronger coherent-orbit theorem is an elementary written argument, **not yet a full all-parameter Lean source certificate or an externally peer-reviewed claim of novelty**.

## Why the original problem remains open

For the authentic blank tape, the section entry is the **single fixed integer 10**. Its future is a single deterministic orbit. Our theorem allows selecting a different, arbitrarily large starting state `x≡10 (mod m)` for each modulus and target. Those chosen starts need not be blank-reachable. Even this coherent finite-trajectory mixing **cannot be applied to the exact start 10** and neither forces nor forbids any hit of a halting power of two.

The theorem isolates a stronger methodological boundary: proof methods based solely on congruence information uniformly valid for *every sufficiently large start in the same residue class* cannot exclude these finite reachable residues. A solution of Sheep and hence BB(6) must exploit information that distinguishes the exact blank-origin state and its unbounded correlated trajectory.
