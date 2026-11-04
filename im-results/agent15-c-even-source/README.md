# Machine C: six-of-eight even-right exact inverse and four-gate backward filter

**Agent 15, 2026-11-04. Research status: original-source CI pending.** All claims below concern the original accelerated Machine C section map `BB6.Agent46.secNext` and the genuine blank section seed `(5,1)`. Machine C and BB(6) remain undecided.

## Main structural theorem

For every pair of natural input counters `a,k` and output counters `x,y` satisfying

```
y >= 6, y even, (x+y)%8 != 0, (x+y)%8 != 7,
```

the **complete**, unbounded-depth section inverse is

```
secNext (a,k) = some (x,y)
  <-> a = x+y-2 and k = (y-2)/2.
```

Exactly **six of the eight** coordinate-sum residue classes are covered for every even right counter `y>=6`. This is an exact original-section statement, not a finite search rule. The source `EvenRightUnique.lean` combines the established `SectionAffineInverse` (sum 1 modulo 4) with two new number-theoretic branches:

- `EvenEvenUnique.lean`: `x,y` even and `(x+y)%8!=0`. The only possible high even-bounce depth-zero cost violates parity; any positive depth makes `x+y` divisible by eight. Other source branches are excluded by parity or low-coordinate exceptions.
- `OddEvenUnique.lean`: `x` odd, `y` even, `(x+y)%8=3`. The high odd-bounce depth-zero cost violates parity (using the authentic high-branch guard `a<2*k`); positive depths force `x+y+1` divisible by eight. Other source branches cannot produce the target.

The complete source grammar is [Agent3's `FullSectionInverse.lean`](../agent3-c-bounce-inverse/FullSectionInverse.lean), previously original-source checked. `EvenRightUnique.blank_reach_iff_even_right` proves for every qualifying target that its blank-origin reachability is **equivalent** to that of its unique predecessor. Each inverse edge reduces `x+2*y` by exactly four.

## Stronger general-purpose filter

[FourForcedNormalize.lean](./FourForcedNormalize.lean) adds the even-right `R` gate to Agent3's already-certified odd-low `O`, even-seven `E` and affine `A` forced inverse branches, recursively until no gate applies. Strong induction on `x+2*y` establishes the *exact* unbounded blank-orbit reachability equivalence with the normalized residual. [FourForcedFilter.lean](./FourForcedFilter.lean) then proves an executable sound exclusion: if the residual has odd right counter >=5 and sum residue 1 or 2 modulo four, the input target is absent from **every** blank section time. A false filter value conveys no reachability claim.

The newly added even-right gate covers residue classes unavailable to the previous three-gate normalizer. This is a genuinely stronger source-based reduction at the theorem level. An independent exact-integer Python mirror, enumerating second-family stopping inputs with `m=0..7, j=0..299`, found strict improvements for every `m` tested; this finite enumeration is **exploratory** and not a proof of any universal density.

## Infinite direct nonreachability consequences

[One64Ten.lean](./One64Ten.lean) establishes the exact genuine-blank cylinder

```
forall u>=1, forall t, run secNext t (some (5,1)) != some (1,64*u+10).
```

Its forced `R -> A -> O` inverse chain is

```
(1,64u+10) -> (64u+9,32u+4)
            -> (96u+11,16u+1)
            -> (56u+4,36u+1).
```

The terminal right counter is odd >=37; the coordinate sum `92u+5` is 1 modulo 4, impossible for a post-initial original-source section return. It is also different from the blank initial state `(5,1)`.

[FirstM38.lean](./FirstM38.lean) combines this unbounded section-cylinder theorem with the exact first-family stopping equation `k+3m+4=2^(2m+3)`. When `m=64r+38`, the dyadic RHS and elementary exponential lower bound imply `k>=74`, `k%64=10`; hence **every** corresponding first-family candidate is unreachable from blank. This class lies in the `m%16=6` sector which Agent15's earlier one-sided affine quotient filter could not decide. Its independence from *all* existing repository filters requires further audit, so this is kept here, not in `results/`.

[SecondM0Family.lean](./SecondM0Family.lean) excludes for every `t` the second stopping family input `(64t+15,96t+25)`, corresponding to `(j,m)=(32t+6,0)`. The exact `O -> R` source chain ends in `(168t+36,44t+9)`, which has forbidden odd-right sum residue one. This was not excluded by the previous three-gate *Boolean* filter; other preexisting source or quotient exclusions might overlap.

## Verification and limitations

The **pure arithmetic branches** were compiled locally with **Lean 4.36.0-rc2**, yielding no `sorryAx` for their source-grammar criteria. The reachability, four-gate, filter, and parametric exclusion proof scripts were likewise compiled against **explicit source-signature-shaped scratch axioms** for the preexisting repository theorems. This checks their derivations and proof terms conditional on those exact signatures. It is **not** original-source certification; the resulting scratch axiom printouts faithfully name the imported assumed theorems. No claim of full source/kernel certification is made until CI actually compiles them against the unchanged originals with standard axioms only.

The separate manual-only [original-source workflow](../../.github/workflows/agent15-c-even-inverse.yml) compiles the source inverse and blank-reachability core including `EvenRightUnique`; it is presently **not dispatched**. The four-gate and two cylinder corollaries require the broader Agent3 original-source dependency chain and likewise await a manual source check. Historical published source validations cover those dependencies but cannot substitute for checking these new modules.

The six-of-eight inverse leaves the two high-bounce residue classes `0` and `7` unresolved. Even after normalization, residual states may have genuine unclassified parents. It does **not** settle Machine C nonhalting or establish the exact BB(6).
