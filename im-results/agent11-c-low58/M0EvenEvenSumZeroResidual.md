# m=0 high-ray residual: even-even sum-zero sector

Status: **intermediate source-grammar analysis, not a blank-root closure theorem**. The exact all-source inverse grammar is available. Forward-only parent necessity and two parameterized m=0 root-exclusion candidates are now encoded in [M0EvenEvenSumZeroParents.lean](M0EvenEvenSumZeroParents.lean) and [M0EvenEvenSumZeroRays.lean](M0EvenEvenSumZeroRays.lean), with the combined exact criterion in [CThreeDiagonalM0SumZeroFull.lean](CThreeDiagonalM0SumZeroFull.lean). None of these new modules has yet passed original-source Lean compilation/CI; treat them as unverified drafts. The parent theorem covers S>2 and S%4!=0 and derives reachability(A_s) -> reachability(L_s) or reachability(B_0,s). The two ray theorems propose all-time exclusions j=1895 (mod 2048) and j=359 (mod 8192), and the final module composes them into the latest exact six-sector halting iff. Do not count these as source-certified until the manual workflow passes.

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

## Generic even-even sum-zero inverse grammar

The same source calculation gives a reusable classification beyond this one ray. For any target `(x,y)` with x and y even, `y>=6`, and `8 | (x+y)`, the complete source-parent alternatives are:

```text
(1) a=0, k>=2, and for some odd n:
      x+y = 2^(n+3)
      2*k + 9 + 3*n = x+2*y

(2) direct/low:
      a = x+y-2
      k = (y-2)/2

(3) a>=2 even, k>=1, 2*k>a, and for some odd n:
      x+y = 2^(n+1)*(a+2)
      2*k + a + 7 + 3*n = x+2*y.
```

There are no a=1 or odd-a high-bounce parents: in those branches the source grammar requires the odd quantity `x+y+1` to equal an even power-of-two multiple. The a=0 and even-a bounce depths are both forced odd by the cost equation's parity. The direct parent is always valid for x>=0 and y>=6. The complete generic iff is a direct specialization of Agent3's `section_preimage_all_iff` but is not yet encoded. `M0EvenEvenSumZeroParents.lean` formalizes only the forward parent necessity for S>2 and S%4!=0, which suffices for the odd-s candidate families below. It does not handle S%4=0 or prove parent converses. The A_s formula below is the closed-form specialization in which the a=0 alternative is arithmetically absent.

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
- The direct branch gives L_s. For every r with 4^r|S, the displayed bounce candidate also satisfies the source guards: q>=3, since q=1 or 2 would make S a power of two; hence a=2q-2>=4. Also q<=S and r<=S, so\n\n  2*k-a = 312+512*s-4*q-6*r >= 312+512*s-10*S = 32+62*s > 0.\n\nThus k>=1 and 2k>a. The exact source branch equations and all guards are algebraically checked. `M0EvenEvenSumZeroParents.lean` now formalizes the forward-only necessity in the subcase S>2 and S%4!=0, but it has not yet passed original-source Lean compilation and does not encode the full generic iff or the S divisible by 4 cases.

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

This is a finite, exact two-branch reduction for the entire odd-t ray, not a bounded inverse-depth approximation. The new Lean draft proves only the forward implication from reachability of A_s to reachability of one of these two parents; it does not prove the converse or a uniform all-time nonreachability result for all odd s. The two specializations s=32v+29 and s=128w+5 are separately encoded as root-exclusion candidates in `M0EvenEvenSumZeroRays.lean`, still awaiting source CI.

## New algebraic subfamily: s=32v+29 (original high-stop j=1895 mod 2048)

The two-parent reduction above yields a further infinite exclusion candidate. Put `s=32v+29` and hence `t=2s+1=64v+59). Then

```text
A_s = (6162+6656v, 4502+4864v)
S   = 1333+1440v.
```

S is odd and not a power of two: modulo 3 it is 1, forcing a hypothetical exponent even; modulo 5 it is 3, forcing the exponent to be 3 modulo 4. Thus A_s has exactly two parents:

```text
L = (10662+11520v, 2250+2432v)
B = (2664+2880v, 6246+6752v).
```

**L branch.** Its sum quotient is
```text
(L.x+L.y)/8 = 1614+1744v = 2*(807+872v),
```
which has 2-adic valuation exactly 1 and is not a power of two. So L has exactly two parents:
```text
D = (12910+13952v, 1124+1216v)
E = (3226+3488v, 5963+6448v).
```
D has even right coordinate and sum `14034+15168v ≡ 2 (mod 8)`; its six-of-eight unique parent is
```text
D' = (14032+15168v, 561+608v),
```
whose right coordinate is odd and whose sum is `1 (mod 4)`. E itself has odd right coordinate and sum `9189+9936v ≡ 1 (mod 4)`. Both D' and E are excluded by `blank_section_odd_image`. Hence L is blank-unreachable, conditional only on the specialized complete parent iff being formalized.

**B branch.** Three forced six-of-eight inverses give
```text
B  = (2664+2880v, 6246+6752v), sum ≡ 6 (mod 8)
D1 = (8908+9632v, 3122+3376v), sum ≡ 6 (mod 8)
D2 = (12028+13008v,1560+1688v), sum ≡ 4 (mod 8)
D3 = (13586+14696v, 779+844v), right odd, sum ≡ 1 (mod 4).
```
The right coordinates of B, D1, D2 are even and at least 6, so the six-of-eight theorem applies at every edge. D3 is excluded by `blank_section_odd_image`. Hence B is blank-unreachable.

Therefore the algebraic parent disjunction would give `¬CReach(A_{32v+29})` for every v. The first two forced inverses from the original high-stop target to A(t) apply for odd t, so this translates to
```text
t = 64v+59
j = 7+32*t = 1895+2048v
k = 3*j+7 = 5692+6144v.
```
Thus the candidate all-time high m=0 exclusion is `j ≡ 1895 (mod 2048)`.

**Status:** the arithmetic and composition are encoded in `M0EvenEvenSumZeroParents.lean` and `M0EvenEvenSumZeroRays.lean`. The source proof is forward-only parent necessity, not a full parent iff. The two all-time high-stop exclusion theorems and their exact-criterion integration are not yet source-CI-certified. Agent24 independently checked the six-of-eight chain arithmetic; Agent3 has been asked to compile and audit the parent lemma. Do not count this family as proven until the original-source manual workflow succeeds.

## Second algebraic subfamily: s=128w+5 (original high-stop j=359 mod 8192)

A second disjoint progression closes by the same parent grammar and forced inverses. Put `s=128w+5`, so `t=2s+1=256w+11`. Since S=28+45s=253+5760w is odd, A_s again has exactly two parents:
```text
L=(2022+46080w,426+9728w)
B=(504+11520w,1182+27008w).
```

For L, its sum quotient is `306+6976w=2*(153+3488w)`, of exact 2-adic valuation 1. Its two parents are
```text
D=(2446+55808w,212+4864w)
E=(610+13952w,1127+25792w).
```
E is odd-right with sum `1737+39744w ≡1 (mod4)`. D has even-right sum `2658+60672w ≡2 (mod8)`, so its unique six-of-eight parent is `D'=(2656+60672w,105+2432w)`, odd-right with sum `2761+63104w ≡1 (mod4)`. Thus L is blank-unreachable.

For B, five forced six-of-eight inverses give
```text
B  = (504+11520w,1182+27008w), sum ≡6 (mod8)
D1 = (1684+38528w,590+13504w), sum ≡2 (mod8)
D2 = (2272+52032w,294+6752w), sum ≡6 (mod8)
D3 = (2564+58784w,146+3376w), sum ≡6 (mod8)
D4 = (2708+62160w,72+1688w), sum ≡4 (mod8)
D5 = (2778+63848w,35+844w), right odd, sum ≡1 (mod4).
```
All right coordinates along B through D4 are even and at least 6, so each six-of-eight inverse applies. D5 is excluded by `blank_section_odd_image`. Hence A_s is blank-unreachable, conditional on the specialized parent-necessity lemmas.

Translating back gives the second candidate high-stop exclusion:
```text
t=256w+11
j=7+32*t=359+8192w
k=3*j+7=1084+24576w.
```
This is disjoint from the `j=1895+2048v` family above. It is now encoded in `M0EvenEvenSumZeroRays.lean` using the same forward-only parent lemma, but remains unverified until original-source CI succeeds.

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

First obtain an original-source compile of `M0EvenEvenSumZeroParents.lean`, `M0EvenEvenSumZeroRays.lean`, and `CThreeDiagonalM0SumZeroFull.lean` through the manual workflow. Fix any proof errors before claiming the two high-stop exclusions. Then handle the remaining odd-s classes (especially s≡7 mod8) and the general S divisible by4 parent tree. The decisive target remains an all-parameter closure of this authentic m=0 stopping family, not another finite residue census.

Related files: `M0FourRoot.lean`, `M0OddRayValTwo.lean`, `M0OddRayDeep.lean`, `CThreeDiagonalM0DeepFull.lean`, Agent24's `EvenEvenInverse.lean`, `ExtraEvenOrbit.lean`, `EvenRightSixOrbit.lean`, and Agent3's `SectionAllInverse.lean`.
