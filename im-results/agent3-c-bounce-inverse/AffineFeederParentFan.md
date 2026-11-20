# Complete inverse-parent fan for the affine feeder line

**Status:** exact paper-level derivation from the source-certified `section_preimage_all_iff` grammar in `SectionAllInverse.lean`. This note is not yet a standalone Lean-compiled theorem. It is a parent classification, **not** a proof that the feeder line is unreachable.

## Why this line matters

The one-left section gate has the exact reduction
`CReach (1) (4*j) ↔ CReach (4*j-1) (2*j-1)`
(`blank_one_four_iff_feeder`). Writing `k=2*j-1`, the right-hand target is the affine line
`F(k) = (2*k+1,k)`, with odd `k`.

For the `a=1` halting targets whose depth is `0 mod 8`, the target's right coordinate is divisible by four, so their blank-root question reduces to genuine reachability of members of this line. Excluding the whole line would therefore close that entire halting-depth sector. Finite orbit scans are not a substitute for this.

## Exact parent fan

Let `k≥5` be odd. If `secNext (a,b) = some (2*k+1,k)`, then the complete source grammar forces the source to be an even-left bounce. In particular there is an even `n` such that

```text
3*k + 1 = 2^(n+1) * (a+2)
2*b + a + 7 + 3*n = 4*k + 1
2 ≤ a, 0 < b, a < 2*b.
```

Conversely, any `n,a,b` satisfying these equations and inequalities is an actual source edge to `F(k)). Thus the exact all-time reachability reduction is

```text
CReach (2*k+1) k
  ↔ ∃ n a b,
      n % 2 = 0
      ∧ a % 2 = 0 ∧ 2 ≤ a ∧ 0 < b ∧ a < 2*b
      ∧ 3*k+1 = 2^(n+1)*(a+2)
      ∧ 2*b+a+7+3*n = 4*k+1
      ∧ CReach a b.
```

For fixed `k,n`, the parent is unique:
```text
a_n = (3*k+1)/2^(n+1) - 2
b_n = (4*k-a_n-6-3*n)/2.
```
The divisibility condition `2^(n+2) ∣ 3*k+1` follows because `a_n` is even. Only finitely many depths can occur, since `2^(n+2) ≤ 3*k+1`; the source inequalities above must still be retained (in particular, a quotient equal to two gives `a_n=0`, which is not in the even-left bounce branch).

### Exhaustion of the other source rows

Put `x=2*k+1`, `y=k`; then `x+y=3*k+1 ≡ 1 (mod 3)` and `x+2*y=4*k+1` is odd.

- The `a=0`, `b≥2` row would give `3*k+1=8*2^m`. Modulo three forces `m` odd, while its cost equation `2*b+9+3*m=4*k+1` forces `m` even. The exceptional `a=0` rows have right coordinate below five.
- The `a=1`, `b≥4` row would give `3*k+2=16*2^m`. Modulo three forces `m` odd, while `2*b+11+3*m=4*k+1` forces `m` even. Its exceptional rows have first coordinate zero or two, unlike `2*k+1≥11`.
- The `a≥2,b=0` and direct rows have target right coordinate two or even, respectively, contradicting odd `k≥5`.
- The odd-left bounce row has `3*k+2=2^m*(2*a+6)`; its left side is odd and its right side even.
- The only remaining row is the even-left bounce displayed above. Its cost equation forces `n` even by parity.

This uses every exceptional and recursive row of `section_preimage_all_iff`; it does not assume a bounded bounce depth.

## Rank decrease and immediate consequences

Use weighted rank `R(x,y)=x+2*y`. Every parent in the fan satisfies

```text
R(F(k)) = 4*k+1
R(a_n,b_n) = 4*k-6-3*n
R(F(k)) - R(a_n,b_n) = 7+3*n > 0.
```

So the full inverse fan is finite and strictly rank-decreasing. It is suitable for a well-founded branching normalizer: retain **all** admissible even depths, recurse on every parent, and stop only at a source-image obstruction or a genuine residual.

Two immediate facts:

1. If `k ≡ 3 (mod 4)`, then `3*k+1 ≡ 2 (mod 4)`, so no admissible `n` exists. Since `F(k)` has first coordinate greater than five, a blank-root visit would require a source predecessor. Hence `F(k)` is not blank-reachable for every odd `k≥5` in this residue class.
2. If `k ≡ 1 (mod 4)`, the `n=0` parent is always admissible:
   `(a_0,b_0) = (3*(k-1)/2, (5*k-9)/4)`.
   Higher even depths are additional alternatives whenever `2^(n+2) ∣ 3*k+1` and the source inequalities hold. In particular, `k ≡ 5 (mod 16)` can admit an `n=2` branch; following only the `n=0` parent is not an all-time reachability equivalence there.

## Specialization to the actual `a=1), depth-`0 mod 8` halting family

Let `d=8*m` be the `a=1` halting-level depth and let `K` be the right counter in the target `(1,K)). The closed form for `haltLevel` gives

```text
K = 2^(d+3) - (3*d+8)/2
  = 2^(8*m+3) - 12*m - 4.
```

The exact one-left predecessor is `(K-1,K/2-1)`, hence it is `F(k)` with

```text
k = K/2 - 1 = 2^(8*m+2) - 6*m - 3.
```

Substitution gives the useful valuation identity

```text
3*k+1 = 2 * (3*2^(8*m+1) - (9*m+4))
v₂(3*k+1) = 1 + v₂(9*m+4).
```

For the valuation equality, note that `0 < 9*m+4 < 2^(8*m+1)` for every `m≥1`; therefore the 2-adic valuation of `9*m+4` is strictly smaller than `8*m+1`, and the two terms in the difference have unequal valuations.

Consequently, a source bounce depth `n=2*j` is divisibility-eligible exactly when

```text
2^(2*j+1) divides 9*m+4.
```

This is a much smaller arithmetic parameter than the enormous feeder coordinate. It also shows why a fixed-depth search cannot settle the whole halting family: for every fixed `j≥0`, the congruence `9*m+4 ≡ 0 (mod 2^(2*j+1))` has one residue class modulo `2^(2*j+1)`, since 9 is invertible modulo every power of two. For fixed `j`, the corresponding `k) tends to infinity along that residue class. Since `a_j≤(3*k-3)/2`, its cost equation gives `2*b_j-a_j=4*k-2*a_j-6-6*j ≥ k-3-6*j`. Thus `k>6*j+3` guarantees `a_j<2*b_j`; for sufficiently large representatives `a_j≥2` as well, and then `b_j>0`. Hence actual parent branches of arbitrarily large even depth occur among these halting targets.

For `m` odd, `9*m+4` is odd, so `v₂(3*k+1)=1` and the feeder has no source parent; this recovers the already-known `d ≡ 8 (mod 16)` exclusion. For even `m), the number and depth of possible parents are governed by the full valuation of `9*m+4`, not merely by `d mod 16`.

## New a=1 residual slice: halt depth `d ≡ 48 (mod 64)`

The valuation specialization above gives a further all-time exclusion beyond the current mod-32 residual.

Write `d=16*s` with `s≡3 (mod 4)`, so `d≡48 (mod 64)` and `s≥3`. The a=1 halting target has

```text
K = 2^(16*s+3) - 24*s - 4
k = K/2 - 1 = 2^(16*s+2) - 12*s - 3.
```

For its feeder `F(k)`,
```text
3*k+1 = 2 * (3*2^(16*s+1) - (18*s+4)).
```
Since `s≡3 (mod 4)`, `18*s+4≡2 (mod 8)`, so `v₂(18*s+4)=1`. The other term is divisible by `2^(16*s+1)), hence `v₂(3*k+1)=2`. The exact odd/odd low-valuation inverse (`oddLowGate`) therefore has the unique parent
```text
P = (3*(k-1)/2, (5*k-9)/4)
  = (3*2^(16*s+1)-18*s-6, 5*2^(16*s)-15*s-6).
```

Both large powers vanish modulo four. Using `s≡3 (mod 4)`,
```text
P.1 ≡ -18*s-6 ≡ 0 (mod 4)
P.2 ≡ -15*s-6 ≡ 1 (mod 4).
```
The global blank-image obstruction `blank_section_no_zeroone` excludes every section state with these residues (equivalently, the complete source grammar has no output in the `(0,1) mod 4` class). Thus P is not blank-reachable; the exact `oddLowGate` equivalence excludes F(k), and the one-left feeder equivalence excludes the original `(1,K)` halting target.

**Conclusion:** every a=1 halting candidate with depth `d≡48 (mod 64)` is excluded. This is outside the current mod-32 residual exclusions (`d≡2 mod 8` and `d≡8 mod 16`). The derivation composes existing source-certified reductions and image invariants, but this new arithmetic composition has not yet been packaged as a standalone Lean theorem.

## What this does and does not settle

This replaces the fixed-depth feeder discussion by a complete finite source-parent fan. It explains precisely why the existing `oddLowGate` normalizer is sufficient only when `v₂(3*k+1)` is two or three: in that range `n=0` is the sole possible even depth. At higher valuation, every admissible `n=0,2,4,…` branch must be retained.

The remaining mathematical task is now explicit: analyze the even/even or even/odd parents `(a_n,b_n)` for **all** admissible `n`, using the exact source grammar and genuine blank-orbit invariants. The `n=0` parent alone does not settle the line, and no finite prefix or finite-depth truncation can do so.

No CI was dispatched and no Lean certification is claimed for this derivation.
