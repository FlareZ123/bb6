# All positive odd high-stopping indices: complete deep-level arithmetic sieve

**Analytical derivation, 9 November 2026; pending generic Lean formalization.** The original Machine C source-image exclusion used below is already Lean certified by Agent 4. Individual families and all-level coverage for m=1 and m=3 are source-certified by Agent 19. The following uniform modular-inverse existence proof for *arbitrary positive odd m* is a paper-level argument, and its density claims are not Lean cardinality certificates.

## Universal theorem

Fix any **positive odd** high-stopping index `m`. Let

```
E=2m+2, P=2^E, A=P-1, B=3P-3m-3.
```

The canonical high-stopping target with parameter `j` has coordinates

```
x(j)=2j+3,
y(j)=P(j+3)-(j+3m+5).
```

For all sufficiently large `j` the target has nonnegative coordinates, and

```
y(j)+2 = A*j+B.                                      (1)
```

For every level `r≥2` with **r even if m≡1 modulo 4, or r odd if m≡3 modulo 4**, define `N_r=2^(r+4)`. Because `A=2^E-1` is odd, it has a multiplicative inverse modulo `N_r`. There is exactly one residue class

```
j ≡ u_r := A^(-1)*(44*2^r-B)    (mod 2^(r+4)).         (2)
```

For every sufficiently large nonnegative `j` in that class, define

```
t = (A*j+B-44*2^r)/2^(r+4),
s = (j-2r-2)/4.
```

By choosing `j` far enough along the positive progression, the numerators are nonnegative. Both are integers: (2) gives divisibility by `2^(r+4)` for `t`. Reducing (2) modulo 4 using `r≥2` and `P≡0 mod4`, we get

```
0 ≡ A*j+B ≡ -j-3m-3 (mod 4),
so j ≡ m+1 (mod 4).
```

The required parity condition on `r` is exactly what makes `m+1≡2r+2 (mod4)`; therefore `s` is an integer. The target is now **exactly** the existing strict-image cylinder

```
(x(j),y(j)) =
(8s+7+4r, 2^r*(16t+44)-2).
```

Agent 4's original-source [`CAllDepthBlank.lean`](../agent4-c-four-step-image/CAllDepthBlank.lean) proves the authentic blank-derived first-return orbit starting at `(5,1)` never enters that cylinder, at any time. Consequently the full infinite arithmetic progression (2), beyond a finite lower cutoff, consists entirely of **genuine high-stopping targets excluded from the Machine C blank orbit**. All the modular calculations above are exact integer arithmetic, not a finite empirical sampling argument.

The result is strongest beyond the preceding dyadic inverse-depth gate. Restrict levels to

```
r ≥ 2m       for m ≡ 1 (mod4);
r ≥ 2m-1     for m ≡ 3 (mod4).
```

Indeed the former gives `v₂(y+2)=r+2≥E`; the latter gives `v₂(y+2)=r+2≥E-1`. In either case the center `j+3m+3=P(j+3)-(y+2)` is divisible by `2^(E-1)`. Every older dyadic condition has `n+4≤E` and requires center valuation exactly `n+2≤E-2`, so **none of these deep levels is removed by the old dyadic sieve**. This is a comparison to that one specified earlier sieve, with no claim about the strongest current combined filters.

## Exact asymptotic densities at each fixed odd m

For fixed `r`, the solution class (2), after discarding its finite prefix, has natural density `2^(-r-4)` among `j≥0`. These residue classes are pairwise disjoint as `r` varies, because on each class

```
y(j)+2=2^r*(16t+44)=2^(r+2)*(4t+11),
v₂(y(j)+2)=r+2.
```

Their union over all deep compatible levels has the exact line density

```
m≡1 mod4: sum_(h≥0) 2^(-(2m+4+2h))
         = 1/(3*2^(2m+2)),

m≡3 mod4: sum_(h≥0) 2^(-(2m+3+2h))
         = 2/(3*2^(2m+2)).
```

Here each level corresponds to one residue progression. Interchanging the countable sum with asymptotic density is justified by a uniform tail bound: any disjoint union beyond level `R` is contained in integers whose shifted target has 2-adic valuation at least `R+2`; equivalently its residue classes form nested congruence tails whose total upper density is bounded by the geometric remainder. This can also be established directly from the unique-root modular map (2), but requires a care with infinitely many residue classes at finite cutoffs. For the special certified levels m=1 and m=3, exact finite-prefix-free coverage is proved in Lean independently of this general density statement.

For `m=1`, the formula gives **1/48**, matched by Agent 19's complete even-depth Lean families. For `m=3`, it gives **1/384**, matched by the r=5,7,9,11 source-certified seed rays and their eight-level return-depth towers. Each positive odd m admits the same all-deep-level arithmetic construction. General arbitrary-m passage from the modular-existence proof to a single Lean theorem remains to be implemented.

## How to apply and what remains open

This is a **necessary high-halting-target sieve** obtained through a proven original-source absence theorem. It still leaves positive-density high targets in every m-line, plus every even m and all low stopping parameters. A complete Machine C decision would require a stronger all-root invariant, a complete backwards decision of the remaining parameters, or a true reachable witness. The exact BB(6) value remains open.

Implementation targets: (i) formalize oddness of `A`, modular existence and uniqueness of (2), and nonnegative witnesses `s,t` in Lean, using the already certified image theorem; (ii) connect this uniform predicate to the latest `highAllowedValSixFull` and full-forced sieves, checking strict nonredundancy against their actual proofs; (iii) use the resulting unlimited high-depth sieve to guide the original-root backwards search rather than enumerating ever larger finite moduli.
