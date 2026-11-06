# Machine C: original-source low-58 rectangle and coupled stopping exclusions

**Status, 2026-11-06:** Lean 4.36.0-rc2, certified against the
unchanged original Machine C section source. The core theorems have only
Lean's standard `propext`, `Classical.choice` and `Quot.sound`
axioms. The resulting exact halting criterion **does not decide Machine C**.

## The source-level mathematical result

Let `CReach x y` denote eventual section reachability from the authentic
blank-derived section seed `(5,1)`, with transition `secNext`.
The theorem in [Rect58Source.lean](Rect58Source.lean) states

```lean
theorem blank_no_rect_58_full (x y : Nat)
    (hx : x%64=1) (hy : y%256=58) :
    ¬ BB6.Agent3.CReach x y
```

The proof uniformly excludes a *two-dimensional infinite rectangle*.
There is no time bound, section bound, predecessor-depth cutoff, or
periodicity assumption. It imports the complete, previously verified
original-source relation `section_preimage_all_iff` from
`SectionAllInverse.lean` and the exact even-right equivalence from
`EvenRightSixOrbit.lean`.

To audit the crucial geometry, write the forbidden target as
`T=(64u+1,256v+58)`. Two forced direct predecessor steps give

```text
T  = (64u+1,         256v+58)
R1 = (64u+256v+57,   128v+28)
R2 = (64u+384v+83,    64v+13)
```

The exact complete section inverse of `R2` admits **only**

```text
A = (32u+224v+46, 16u+144v+28)
B = ( 8u+ 56v+10, 28u+228v+43)
```

because `R2.x+R2.y = 64u+448v+96` has 2-adic valuation
**exactly five**, making the only even-bounce depths `0` and `2`.
Odd-source cases and the special `a=0`, `a=1` branches are excluded
using the complete grammar and exact arithmetic. `B` has odd right
counter at least 43 and coordinate sum congruent to 1 modulo 4,
so the genuine blank orbit cannot reach it. The direct inverse of `A`
is forced to

```text
C = (48u+368v+72, 8u+72v+13).
```

`C` has odd right counter at least 13 and sum 1 modulo 4. It is likewise
blank-unreachable by `Agent3CImage.blank_section_odd_image`.
Both exhaustive parent cases are contradicted, proving the rectangle.
The proof explicitly separates the initial time-zero state.

## Infinite stopping parameters removed

The low section stopping target is
`(1, 2^(2m+3)-(3m+4))`. Every `m%256=150` has right counter 58
modulo 256. [Low58Source.lean](Low58Source.lean) proves the complete
all-time exclusion `blank_no_low_m_150`.

The high section stopping target is
`(2j+3, 2^(2m+2)*(j+3)-(j+3m+5))`. The rectangle's
[high-sector theorem](Rect58Source.lean) excludes every pair satisfying

```text
m ≥ 3
j % 32 = 31
(j + 3m + 5) % 256 = 198
```

as its left coordinate is 1 modulo 64 and its right coordinate is
58 modulo 256. This is an unbounded coupled two-parameter family.

A second exact independent proof, [Low14Source.lean](Low14Source.lean),
eliminates every target `(1,64t+14)`. Hence all low indices
`m%64=58` are excluded. The first-target exceptional inverse parents
are checked explicitly. The base case `t=0` uses the source theorem
excluding blank-reachable right counter 2. This theorem is valid,
although this sector was already rejected by the tested M512 quotient.

[JointC58.lean](JointC58.lean) incorporates both low restrictions and
the high rectangle restriction into a **lossless halting equivalence**
built from [Agent23's C26 exact criterion](../agent23-c-low26/JointC26.lean).
Its low predicate is

```text
C26.lowAllowed(m) ∧ m%64 ≠ 58 ∧ m%256 ≠ 150
```

and its high predicate is

```text
C26.highAllowed(j,m) ∧
¬(m≥3 ∧ j%32=31 ∧ (j+3m+5)%256=198).
```

The fixed-target Boolean predicate remains exact. The existential search
over unbounded indices remains mathematically unresolved. The independent
[ValSixJointFull](../agent3-c-bounce-inverse/ValSixJointFull.lean)
criterion has additional restrictions and is **not yet merged** into
this new C58 branch; do not treat either document as subsuming all of
the other's high predicates.

## Formal verification and source dependency

| CI run | Proved source claim | Result |
| --- | --- | --- |
| [42280559453](https://github.com/FlareZ123/bb6/actions/runs/42280559453) | low `m%256=150` root exclusion | success |
| [42282006382](https://github.com/FlareZ123/bb6/actions/runs/42282006382) | low `m%64=58` root exclusion | success |
| [42283365249](https://github.com/FlareZ123/bb6/actions/runs/42283365249) | full 2D rectangle and high gate exclusion | success |
| [42282621087](https://github.com/FlareZ123/bb6/actions/runs/42282621087) | low-only exact C58 halting iff | success |

The source workflow is
[`agent11-c-low58.yml`](../../.github/workflows/agent11-c-low58.yml).
The integrated proof workflow is
[`agent11-c58-joint.yml`](../../.github/workflows/agent11-c58-joint.yml).
Both compile the authentic Machine C source from the repository.

## Comparison with the finite M512 quotient

The independent finite quotient algorithm in
[`QuotientRectCensus.cpp`](../agent19-c-odd-dyadic/QuotientRectCensus.cpp)
was rerun locally with the same transition and residue-abstraction rules
and a print of `seen[idx({x,y,0})]` for the new rectangle.

At `M=512`, the quotient has **27,858,704** reached abstract states and
**221,572,376** generated edges. **All 16** rectangle cells
`x∈{1,65,129,193,257,321,385,449}` and `y∈{58,314}` are
quotient-admitted. In particular both `(1,58,0)` and `(1,314,0)`
are admitted. This is an empirical finite-computation statement,
not a formal proof of the quotient implementation. The Lean theorem
proves the full original-source cylinder unreachable despite every
one of these quotient admissions.

In contrast, the finite M512 quotient rejected all tested
`x=1, y%64=14` residues. This makes the low-14 theorem a useful
independent source certificate and the low-58 rectangle the
clearer advance over that particular abstraction.

The [joint proof](JointC58.lean) also proves `old_low_admits_150`:
**every** parameter `m=256r+150` passed Agent23's earlier C26
low predicate. The same file proves these parameters survive the
separate ValSix low 128-divisibility filter.

## Boundaries and next research decisions

This is a source-exact nonreachability result for one formal Machine C
section family and two corresponding stopping sectors. It gives
neither an upper bound for all six-state machines nor a proof that
Machine C never halts. Other low/high stopping parameter families remain.

Next useful steps are to merge the rectangle into the current
ValSixFull combined certificate, prove explicit independence of the
high sector from all earlier formal high restrictions where possible,
and look for further quotient-admitted rectangular sectors using exact
2-adic inverse arithmetic rather than finite-step searches.
