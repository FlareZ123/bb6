# Machine C first low-stop family: exact first inverse fan for m = 8t + 3

**Status:** exact arithmetic specialization of the original section inverse grammar. This is a structural reduction, **not** a blank-root exclusion or a Machine C decision. No Lean source proof of the new specialization has yet been compiled.

## Target and exact unique predecessor

The first-family stopping condition is
```
K_m + 3m + 4 = 2^(2m+3),
T_m = (1,K_m).
```
Restrict to `m=8t+3`, and put
```
v = 2^(2m) - (3t+2).
```
Since `3m+4=24t+13`,
```
K_m = 2^(2m+3) - (3m+4) = 8v+3.
```
Here `v>0` for every `t≥0`: `3t+2<16t+6=2m` and `4^m>4m` for `m≥3`.

The complete original-source inverse predicate `section_preimage_all_iff` forces the **unique** predecessor of `T_m` to be
```
P_t = (4v,6v).
```
Indeed, for target `(1,8v+3)`, the zero-left branch would require `8v+4` divisible by eight; the one-left and odd-left bounce branches require the odd number `8v+5` to be divisible by sixteen; and the direct branch requires an even right output. In the even-left bounce branch,
`8v+4 = 2^(n+1)(a+2)` with `a` even. Its exact 2-adic valuation is two, so `n=0`; the cost equation then gives `a=4v` and `k=6v`.

This is an all-natural necessary-parent statement for the authentic Machine C section relation, not a finite-run observation.

## Complete parent fan of the even/even state

The state `P_t=(4v,6v)` has positive even coordinates and right coordinate at least six. Apply the complete source-parent classification
`BB6.Agent3ParentFan.even_even_parent_fan` from
[`EvenEvenParentFan.lean`](../agent3-c-bounce-inverse/EvenEvenParentFan.lean).

Its possible parents are:

1. **Direct parent**
   ```
   D_0 = (10v-2, 3v-1).
   ```

2. **Zero-left parent:** impossible, because its equation would make `10v` a power of two times eight, whereas `10v` has a factor five.

3. **Even-left bounce parents:** exactly the odd depths `n` in the range
   ```
   1 ≤ n ≤ s-1,   n odd,
   s = v2(v) = v2(3t+2).
   ```
   For each such `n`, the parent is
   ```
   a_n = 5v/2^n - 2
   k_n = (16v - a_n - 7 - 3n)/2.
   ```
   These are genuine natural source parameters satisfying `a_n≥2` and `2k_n>a_n`. Indeed, `v/2^n` is even, so `a_n` is an even integer at least eight; `k_n` is integral because `n` is odd; and
```
2k_n-a_n = 16v - 10v/2^n - 3(n+1) ≥ 11v - 6m > 0.
```
Here `n<2m` and `v>3m` for `m≥3`. Conversely, the complete parent fan forces every even-left bounce parent to have precisely this form and depth range.

The valuation identity follows from
`v=2^(2m)-(3t+2)` and
`0<3t+2<2^(2m)`: the large power of two has strictly higher 2-adic valuation than the subtracted positive term.

Consequently the first parent fan has exactly
```
1 + floor(s/2)
```
members: one direct parent and one bounce parent for each odd `n≤s-1`.

## The fan depth is genuinely unbounded

Because three is invertible modulo every power of two, for every `s≥1` there are infinitely many `t` with
`v2(3t+2)=s`. Thus the number of possible immediate parents of `P_t` is unbounded over the low stopping family `m=8t+3`.

This rules out any proof strategy that assumes a fixed finite list of even-left bounce depths will handle the entire `m≡3 (mod 8)` low family. It also explains why deeper inverse closures can change sharply between neighboring parameter cylinders.

## What remains

The unique first parent of `T_m` is not enough to prove `T_m` unreachable. Every branch in the complete fan of `P_t` must still be pulled back, and subsequent even/even sum-zero states can create **nested** valuation-controlled fans.

A closely related phenomenon is documented in
[`U5ResidualTwoAdicProfile.md`](../agent3-c-bounce-inverse/U5ResidualTwoAdicProfile.md): an exact affine valuation controls the first fan, while a second affine valuation controls a deeper even/even sum-zero fan and is itself unbounded. The useful next step here is therefore a parameter-uniform recursive description of the subsequent fans, not another isolated residue cylinder.

A scratch exact-parent search found strongly nonuniform reverse-cone sizes (for example, the `m=667` case exceeded 100,000 distinct states and depth 998 at the search cap). This is only exploratory computational evidence; it is not used in the derivation above and does not establish a nonreachability claim.

## Source and trust boundary

The mathematical reduction uses the repository's exact inverse grammar:

- [`FullSectionInverse.lean`](../agent3-c-bounce-inverse/FullSectionInverse.lean), which derives the complete inverse predicate from the original `secNext`;
- [`EvenEvenParentFan.lean`](../agent3-c-bounce-inverse/EvenEvenParentFan.lean), which gives all parents of positive even/even targets with right coordinate at least six;
- [`EvenRightUnique.lean`](../agent15-c-even-source/EvenRightUnique.lean), which collapses the nonexceptional even-right sector to its direct parent.

The formulas in this note are algebraic consequences of those source-certified predicates, but this new `m=8t+3` specialization itself is **not yet Lean-formalized or CI-accepted**. It does not prove that any of the candidate targets is absent from the blank-origin orbit, and it does not resolve Machine C or BB(6).
