# m=0 high-ray residual: even-even sum-zero sector

Status: **intermediate source-grammar analysis, not a blank-root closure theorem**. The exact all-source inverse grammar is already available; this note specializes it to the residual below. The specialization and reachability disjunction are algebraically derived but have not yet been added as new Lean theorems. Do not promote a reachability conclusion beyond the explicitly stated source-certified lemmas.

## Residual after the first two forced inverses

For the high m=0 stopping ray `j=7+32t, k=3j+7`, the target is `(17+64t,28+96t)`. The first two exact inverse gates give

```text
(17+64t, 28+96t)
  <- (43+160t, 13+48t)
  <- A(t) := (26+104t, 18+76t).
```

For odd `t=2s+1`,

```text
A_s := A(2s+1) = (130+208s, 94+152s)
A_s.x + A_s.y = 8*S,       S := 28+45s
A_s.x + 2*A_s.y = 318+512s.
```

Thus `A_s` is even-even with coordinate sum 0 modulo 8. This is exactly the case not covered by the existing nonzero-sum even-even inverse theorems:
- `EvenEvenUnique.section_even_even_iff_affine` requires the sum not be 0 modulo 8;
- `ExtraEvenOrbit.eveneven_nonzero_blank_reach_iff` has the same nonzero-sum restriction;
- Agent24's six-of-eight even-right normalizer also leaves the even-even sum-0 residue.

The finite six-sector census stops at this residual for odd `t`; it does not decide blank-root reachability there.

## Complete specialized incoming-parent grammar

The relevant all-source theorem is Agent3's `section_preimage_all_iff` in `im-results/agent3-c-bounce-inverse/SectionAllInverse.lean`. Specializing its cases to `A_s` gives the following complete parent list.

**Direct/low parent**

```text
L_s = (A_s.x + A_s.y - 2, (A_s.y - 2)/2)
    = (222+360s, 46+76s).
```

**Even-a bounce parents**

Every remaining possible parent has an even first coordinate `a >= 2`, lies in the high branch `2*k>a`, and has an odd bounce depth `n=2r+1`. For each `r>=0` with `4^r | S`, write `q=S/4^r`; the corresponding parent is

```text
B_{r,s} = (2*q - 2, 155 + 256*s - q - 3*r).
```

There are no other source parents. In particular, the exact specialization is

```text
secNext(a,k) = some A_s
  iff (a,k)=L_s
      or exists r q, S=4^r*q
          and a=2*q-2
          and k=155+256*s-q-3*r.
```

The divisibility condition is finite for each s: `r=0,...,floor(v2(S)/2)`. Hence the number of bounce parents is `floor(v2(S)/2)+1`, and the total number of incoming parents is `floor(v2(S)/2)+2`.

**Derivation from the complete source grammar.**

- The `a=0` branch would require `S=2^n`. This is impossible: `S=28+45s ≡ 1 (mod 3)` forces n even, whereas `S ≡ 3 (mod 5)` forces `n ≡ 3 (mod 4)`.
- The `a=1` branch and the odd-`a` high-bounce branch require the odd number `A_s.x+A_s.y+1=8S+1` to equal an even multiple of a power of two.
- The small exceptional branches and `k=0` cannot produce a target whose second coordinate is at least 94.
- In the even-`a` high-bounce branch, the exact grammar gives

  ```text
  8*S = 2^n * (2*a+4)
  2*k + a + 7 + 3*n = A_s.x + 2*A_s.y = 318+512*s.
  ```

  The second equation forces n odd. Put n=2r+1. The first equation becomes `S=4^r*q` with `q=(a+2)/2`, so `a=2q-2`; solving the cost equation gives `k=155+256s-q-3r`.
- The direct branch gives L_s. Conversely, the displayed candidates satisfy the exact source branch equations and guards; this last direction is part of the specialized iff still to be formalized in Lean.

## Odd-s specialization: exactly two parents

If `s` is odd, then `S=28+45s` is odd, so `4^r|S` forces `r=0`. Thus the full incoming list has exactly two parents:

```text
L_s   = (222+360s, 46+76s)
B_0,s = (54+90s, 127+211s).
```

Consequently the intended blank-root theorem is the exact disjunction

```text
CReach(A_s) <-> CReach(L_s) or CReach(B_0,s),    s odd.
```

This is a finite, exact two-branch reduction for the entire odd-t ray, not a bounded inverse-depth approximation. The specialized parent iff and this reachability iff remain to be Lean-formalized.

## Important correction to the earlier scratch derivation

The previous draft had two arithmetic errors. The even-a bounce cost is `2*k+a+7+3*n = x+2*y`, **not** `2*k+a+9+3*n = x+2*y`. Therefore

```text
B_0,s = (54+90s, 127+211s),
```

not `(54+90s,126+211s)`. The right coordinate is odd exactly when **s is even**, not when s is odd. All earlier claims using the old parity of B_0,s are withdrawn.

## What existing root invariants now say

- L_s has coordinate sum `268+436s`. For even s this is 4 modulo 8, so the existing even-even unique-parent theorem reduces L_s further. For odd s it is 0 modulo 8, leaving the sum-zero case unresolved.
- For even s, B_0,s is even-left/odd-right and its sum is `181+301s ≡ 1+s (mod 4)`. The all-time odd-image theorem `blank_section_odd_image` excludes it when `s ≡ 0 (mod 4)`, but not when `s ≡ 2 (mod 4)`.
- For odd s, B_0,s is even-even. Its sum is `181+301s ≡ 5(1+s) (mod 8)`, i.e. 2, 4, 6, 0 as `s ≡ 1,3,5,7 (mod 8)`. Agent24's six-of-eight even-right normalizer therefore forces its affine parent for `s ≠ 7 (mod 8)`; the `s ≡ 7 (mod 8)` subfamily is another sum-zero case.
- These normalizations do not remove L_s for odd s. No all-time nonreachability claim for A_s, L_s, or B_{r,s} follows yet.

## Next useful step

Formalize the specialized complete parent iff and its blank-root disjunction first. Then analyze L_s and the surviving B_{r,s} together, using the existing source-certified even-right, even-even, odd-image, and odd-even inverse rules. The decisive target is an all-parameter closure of this authentic m=0 stopping family, not another finite residue census.

Related files: `M0FourRoot.lean`, `M0OddRayValTwo.lean`, `M0OddRayDeep.lean`, `CThreeDiagonalM0DeepFull.lean`, Agent24's `EvenEvenInverse.lean`, `ExtraEvenOrbit.lean`, `EvenRightSixOrbit.lean`, and Agent3's `SectionAllInverse.lean`.
