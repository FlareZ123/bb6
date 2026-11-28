# Raw56 leaf 17557: exact three-return rewrite rules and ternary trace grammar

Literal partial machine:

```
1RB1LA_1RC1RB_0RD0RC_1LD1LE_1LF0LE_0LA---
```

Only F1 is undefined. This note isolates exact local rewrites that explain the
new dyadic/ternary computational structure. The local rewrites below are
ordinary transition-table derivations. The final infinite substitution claim
is **not yet proved**; `analyze_17557_dyadic.py` checks it only through the
finite prefix ending at `C_11`.

## A-return events

Take an A-state configuration with the head on cell 0, whose symbol is 0.
An **A-return segment** runs until A next scans a 0. In every segment seen in
the dyadic family, F reads 0, so the partial machine remains defined.

Group three consecutive A-return segments into one triad. Let `I` mean that
D's first scanned symbol in that segment is 1, and `Z` mean it is 0. The
checked trace has only two triads:

- **A-triad:** `IZI`
- **B-triad:** `ZZI`

The following two local rewrites account for these triads.

## Exact A-triad rewrite

Suppose cell 0 is scanned in state A and the right tape begins

```
1^a 0 1^b 0 1^c 0^z R
```

with `b >= 5`, `c >= 1`, and `z >= 2`. (Here `R` is an arbitrary
unchanged suffix.) The first return is an I-segment: B fills the first
separator, C erases the `b`-block, and D immediately sees the first 1 of the
`c`-block. The second return is Z and the third is I.

For **b >= 6**, after the three returns the head is at coordinate
`a + b - 4`, again in state A on 0. Relative to the new head, the tape is

```
left, near -> far:  0^(b-6) 1^(a+2) [old left context]
right:               1^2 0 1^(c+5) 0^(z-2) R
```

and all three F reads are 0. The triad uses exactly
`a + b + 2*c + 26` primitive steps.

The boundary case **b = 5** performs the carry. If the old left context begins
with `1^d 0 L` (near to far), A's final left sweep crosses those `d` ones.
After the triad the head is on that 0, at coordinate `-d-1`, and the right
tape is

```
1^(d+a+4) 0 1^(c+5) 0^(z-2) R.
```

The context beyond the new head is unchanged. This is the mechanism that
merges a completed local digit into the block on its left. Its cost is exactly
`2*a + 2*c + d + 33` primitive steps.

## Exact B-triad rewrite

Suppose the head is again A on cell 0, with at least seven 0s immediately to
its left, and the right tape is

```
1^a 0 1^b 0^z R
```

where `a >= 2`, `b >= 1`, and `z >= 2`. The three return segments have
pattern `ZZI`. After them the head is exactly seven cells to the left of its
starting position, again A on 0. Seven cells are consumed from the left zero
run, while the right tape becomes

```
1^2 0 1^5 0^(a-1) 1^(b+3) 0^(z-2) R.
```

Again all three F reads are 0. In particular, the first two Z-segments stop E
inside a zero runway of sufficient length, and the final I-segment sends F
onto the cell just erased by C. The triad cost is exactly
`2*a + 2*b + 29` primitive steps.

These formulas can be checked directly by following A0/B/C/D/E/F across the
displayed blocks; no asymptotic or simulation assumption is used in the local
rewrites.

## Dyadic checkpoints and the observed ternary grammar

The blank run reaches the finite-checked configurations

```
C_n:
  time T(n) = 4*4^n + 8*3^(n-1) - 7*2^n - 1
  state A
  head 5 - 2^(n+2), on blank
  blank strictly to the left
  right tape 1^(2^n-2) 0 1^(2^(n+1)-3) 0 1^(2^(n+1)-1)
```

for every `2 <= n <= 11` checked by the literal primitive-step simulator.

Let `W_n` be the A/B triad word between `C_n` and `C_(n+1)`. The same
literal run verifies through epoch 10 that

```
W_2 = ABBA
sigma(A) = ABA
sigma(B) = BBA
W_(n+1) = sigma(W_n).
```

Equivalently, with A=0 and B=1, a substituted symbol `x` produces
`[x,1,0]`. Hence the checked word has

```
|W_n| = 4 * 3^(n-2),
#A(W_n) = #B(W_n) = 2 * 3^(n-2),
```

and exactly `4*3^(n-1)` A-return segments in epoch n. This is the structural
source of the factor `3^(n-1)` in the observed clock formula.

## Fixed renormalization is false at level 10→11

The original level map `rho` is an exact finite-prefix phenomenon, not an
all-level conjugacy. A literal primitive-step replay of the partial machine
finds the arithmetic obstruction.

The old left map doubles every 1-run and maps a finite zero-run
`z=8*q+r` by

```
rhoZero(z) = 16*q+r       if r <= 6
rhoZero(z) = 16*q+15      if r = 7.
```

At epoch 10 triad boundary **k=3280**, primitive time **6,134,105**, the
literal machine is at a B-triad start with

```
left  = 0^14 1^1024
right = 1^2 0 1^5 0^5 1^16 0^7 1^32 0^15 1^64 0^31
        1^128 0^63 1^256 0^127 1^512 0^255 1^3071.
```

The exact B rewrite consumes seven left zeros. At the next low boundary
**k=3281**, time **6,134,148**, the left side is `0^7 1^1024`.

Its corresponding level-11 boundary is **k=9843=3·3281**, primitive time
**24,349,044**. Literal replay gives

```
actual high left = 0^7  1^2048
old-rho prediction = 0^15 1^2048.
```

The right side agrees with the old `rho` prediction exactly:

```
1^6 0 1^13 0 1^16 0^7 1^32 0^15 1^64 0^31
1^128 0^63 1^256 0^127 1^512 0^255 1^1024 0^511 1^6143.
```

Thus the fixed-map conjecture fails by exactly **eight cells in one left
zero-run**. `analyze_17557_defect.cpp` dynamically finds the epoch-10 B
runway with residue 6, replays the literal transition table to the
corresponding high boundary, and asserts this mismatch. It aborts if the
undefined F1 slot is reached.

The failure is already forced by the exact local B formula. For `ell>=7`,
fixed conjugacy would require

```
rhoZero(ell-7) = rhoZero(ell)-15.
```

This holds for every residue of `ell mod 8` except **6**. At `ell=14`,
`rhoZero(7)=15` whereas `rhoZero(14)-15=22-15=7`. The discrepancy is
exactly 8. Similarly, the A-carry identity
`rhoZero(ell-1)=rhoZero(ell)-1` fails exactly for
`ell ≡ 7 (mod 8)`, again by 8. The normal-A identity
`rhoZero(b-6)=2*b-11` holds on the observed normal-A family
`b ≡ 5 (mod 8)`.

The arithmetic core is now independently kernel-checked in
`Raw56LE17557RhoArithmetic.lean` with local Lean 4.36.0-rc2. Besides the
regular identities and exact iff characterizations of the two exceptional
residues, it proves the defect transition equations directly:

- an unmarked residue-6 B runway creates `rhoZero(next)-8`;
- a marked nonexceptional B runway preserves the same `-8` defect;
- a marked residue-7 carry cancels the defect exactly;
- a marked nonexceptional carry preserves it.

The printed axiom profiles contain only Lean's standard quotient/propositional
axioms (and `Classical.choice` on the iff characterizations), with no
`sorryAx`. The remaining difficulty is therefore structural reachability of
the run grammar and the marked-run relation, not the modular arithmetic.

## A one-defect relation explains the prefix, but fails at rank 8

The first repair is highly structured. Primitive replay through the
level-11→12 comparison shows that the right-side transformation remains
exact at every compared boundary, every left 1-run still doubles, and left
run shape is unchanged. Every discrepant boundary there has exactly one
zero-run shorter than the old `rhoZero` prediction by 8.

A streaming lockstep replay using only the exact A/B triad formulas extends
that **finite prefix** through level 15. It replays one low macro against its
three high macros and reports zero right-side failures, zero relation-shape
failures and zero multi-mark boundaries through the level-15→16 comparison:

| low→high level | unmarked | mark 0 | mark 1 | mark 2 | mark 3 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 10→11 | 26,243 | 2 | 0 | 0 | 0 |
| 11→12 | 78,703 | 28 | 2 | 0 | 0 |
| 12→13 | 235,947 | 216 | 34 | 0 | 0 |
| 13→14 | 707,047 | 1,224 | 314 | 4 | 0 |
| 14→15 | 2,117,863 | 5,724 | 2,098 | 80 | 0 |
| 15→16 | 6,341,515 | 23,520 | 11,390 | 860 | 8 |

The corresponding complete one-defect lifetimes seen in this prefix are
exactly `E_r=sigma^r(BA)` for ranks `r=0..5`. Their lengths are
`2·3^r`; the largest observed mark depth is `ceil(r/2)`.
`Raw56LE17557EpisodeWord.lean` kernel-checks the independent substitution
bookkeeping: `E_(r+1)=sigma(E_r)`, `|E_r|=2·3^r`, and every `E_r`
contains exactly `3^r` A macros and `3^r` B macros.

The one-defect interpretation is **not** an all-level invariant. The exact
triad rewrite grammar predicts, and a targeted reachable-state replay
confirms, a second obstruction at rank 8.

Start from the exact epoch-18 checkpoint and replay the exact A/B rewrites to

```
k = 3280 * 3^8 = 21,520,080.
```

This is the start of the rank-8 substituted defect episode. Pair that
reachable low state with its ordinary `rho` image. The pair initially has
no defect and the right relation is exact. At episode offset **3280**, the low
state has a B runway of length **22** while the current pair already has an
8-cell front defect. After the low B and its high-side `BBA` block,

```
low next zero     = 15
actual high zero  = 15
rhoZero(15)       = 31
```

so the defect is now **16 cells**, not 8. The right relation still agrees
exactly. At episode offset **9841**, two distinct left zero-runs each carry an
8-cell defect simultaneously. Therefore both “one token” and “one weighted
token” are false as global invariants.

`analyze_17557_defect_vector.cpp` reproduces this derived-macro closure
counterexample. It then checks the entire `|E_8|=13,122` macro episode with
the more general relation

```
high zero_i = rhoZero(low zero_i) - 8 * weight_i,
weight_i ∈ Nat.
```

Across that full episode the right map remains exact, every left discrepancy
is a positive multiple of 8 on a zero-run, the maximum number of simultaneous
nonzero weights is **2**, the maximum weight is **2**, and all weights return
to zero at the end of the episode. This is derived-macro evidence rather than
a primitive-machine/source theorem, but it is an exact closure test for the
local rewrite system.

The same derived-macro closure test has now been iterated on complete
substituted episodes through **rank 13**. For ranks 8, 9, 10, 11, 12 and 13,
with respective episode lengths 13,122; 39,366; 118,098; 354,294;
1,062,882; and 3,188,646 macros, every comparison keeps the right relation
exact, every left discrepancy remains an 8-multiple zero-run defect, the
maximum simultaneous number of nonzero weights stays **2**, the maximum
weight stays **2**, and the episode ends with the all-zero weight stack.
`analyze_17557_defect_vector.cpp` reproduces this stress test. These rows
remain local exact-rewrite evidence, not a primitive-source induction theorem.

The arithmetic explains the new state naturally. On a front zero-run:

- ordinary B residues preserve its defect weight;
- exceptional B residue 6 increments the front weight by one;
- ordinary A-carry residues preserve the front weight;
- exceptional A-carry residue 7 decrements a positive front weight by one;
- normal A prepends a fresh zero-run of weight zero;
- exact zero-run deletion pops the corresponding weight, subject to the
  reachable guard that the disappearing run has weight zero.

`Raw56LE17557DefectStack.lean` now lifts these scalar laws to the whole
aligned zero-run/weight stack and is locally checked by Lean 4.36.0-rc2.
Two guard equivalences make the intended semantic induction especially
direct: the B arithmetic bound is equivalent to the related high runway
having at least **15** cells, exactly what the high `BBA` block consumes;
and, under the necessary residue-7 positive-weight condition, the carry
bound is equivalent to the related high front zero-run being nonempty.
Moreover, the exact deletion cases no longer require a separate pop guard:
at low B-runway length 7, the semantic 15-cell high-runway condition forces
the front weight to be zero; at low carry-runway length 1, high-side
nonemptiness forces the front weight to be zero. Normal A's residue-5 rule
is also packaged as a zero-weight stack push. The weighted relation preserves
every zero-run residue modulo 8 exactly, and under the natural non-underflow
bound the defect weight is recoverable uniquely from the low/high run pair.
More precisely Lean proves
`high/8 = 2*(low/8) + [low mod 8 = 7] - weight`.
Thus the residue automaton is unchanged by introducing weights: the new state
is exactly a quotient-level carry deficit. The file therefore leaves the reachable
zipper shape, normal-A residue-5 condition, and residue-7 positive-weight
condition as the principal unresolved semantic obligations.

Thus the next proof object is a **stack/vector of nonnegative defect weights**,
one aligned with each finite left zero-run, rather than a single marked run.
The finite-prefix one-token rules and `Raw56LE17557DefectRelation.lean`
remain useful special cases for weights in `{0,1}` with support size at most
one, but they are not the final conjugacy domain.

## Right-side level map

The right transformation remains the fixed component. For
`1^a1 0^z1 1^a2 0^z2 ... 1^am`, `m>=2`:

- `a1 -> 2*a1+2`, `z1 -> 2*z1-1`;
- if `m=2`, final `a2 -> 2*a2+4`;
- if `m>=3`, `a2 -> 2*a2+3`, `z2 -> 2*z2-1`;
- later nonfinal 1-runs double and later zero-runs map `z -> 2*z+1`;
- final `a -> 2*a+1`.

The dyadic checkpoints still obey this right transformation and the checked
triad word still follows `sigma(A)=ABA`, `sigma(B)=BBA`. The
counterexample invalidates only the context-free left zero-run map.

## Remaining proof obligation

Define a symbolic relation on paired low/high triad-boundary zippers with:

1. the fixed right-run relation;
2. doubled left 1-runs;
3. a nonnegative defect-weight vector aligned with the finite left zero-runs;
4. zero-run equation `high_i = rhoZero(low_i) - 8 * weight_i`;
5. local stack rules for normal-A push, exact-run pop, residue-6 B increment,
   and residue-7 carry decrement;
6. a reachable guard strong enough to keep every subtraction nonnegative and
   justify zero-weight pops.

Then prove that one low A or B triad corresponds to `ABA` or `BBA` on
the high side while preserving this weighted-stack relation. The finite base
epoch `C_2 -> C_3` is already exact. The rank-8 replay shows why any proof
domain restricted to one defect or one marked run cannot be inductive.

The old fixed map and the one-token repair should not be revived as global
claims. The weighted defect-stack relation is the current smallest known
proof target for leaf 17557.
