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

## Level-raising renormalization

There is a substantially sharper finite-checked self-similarity. Work in the
translation-invariant zipper coordinates `Z0`, so absolute head position is
discarded. At each triad boundary, write the left and right tape as
near-to-far alternating run-length lists.

For every corresponding boundary checked from epochs 2→3 through 6→7, the
boundary at position `k` is carried to boundary `3k` at the next level by
one fixed run-length map `rho`.

On the right, for
`1^a1 0^z1 1^a2 0^z2 ... 1^am` with `m >= 2`:

- `a1 -> 2*a1+2`, `z1 -> 2*z1-1`;
- if `m=2`, the final `a2 -> 2*a2+4`;
- if `m>=3`, `a2 -> 2*a2+3`, `z2 -> 2*z2-1`;
- later nonfinal 1-runs double, later zero-runs map `z -> 2*z+1`;
- the final 1-run maps `a -> 2*a+1`.

On the left, every 1-run doubles. Every observed zero-run except the fixed
anchor `3` has a unique representation

```
z = 8*q + s,   s in {-1,0,1,2},
```

and maps to `16*q+s`; the anchor `3` remains `3`.

This map sends the checkpoint tape in `C_n` exactly to the checkpoint tape
in `C_(n+1)`: the three right 1-run lengths transform as

```
2^n-2       -> 2^(n+1)-2
2^(n+1)-3   -> 2^(n+2)-3
2^(n+1)-1   -> 2^(n+2)-1.
```

Moreover, the checked macro orbit satisfies the conjugacy pattern

```
rho ∘ A = (A B A) ∘ rho
rho ∘ B = (B B A) ∘ rho
```

at every reachable lower-level boundary in those epochs. This is exactly the
same substitution `sigma(A)=ABA, sigma(B)=BBA` seen in the branch word.
`analyze_17557_renorm.py` reproduces the literal primitive-step audit and
checks the level map on every corresponding triad boundary through level 7.

## Algebraic reduction of the conjugacy

The exact triad formulas reduce the two conjugacy identities to elementary
run-length identities; no long primitive trace is needed once the symbolic
domain is fixed.

For a normal A-triad, the lower second 1-run has
`b in {13,29,61,125,...}`. After level raising it is `2*b+3`.
The high-level sequence is therefore:

```
A:  left zero runway becomes 2*b-3
B:  the runway becomes       2*b-10
A:  boundary b=5 consumes one more zero, leaving 2*b-11.
```

The lower A-triad leaves a zero runway `b-6`; hence the left-side part of
`rho∘A = ABA∘rho` is exactly

```
rhoZero(b-6) = 2*b-11.
```

For the reachable family `b-6 in {7,23,55,119,...}`, this follows directly
from the signed-residue rule. On the right, the same three high triads give

```
1^6 0 1^(rho(c)+13) 0^(rho(z)-6) ...
```

which is exactly `rho` of the lower result
`1^2 0 1^(c+5) 0^(z-2) ...`; the final/nonfinal 1-run cases agree
separately with the right-run rules.

For a B-triad with left zero runway `ell`, the high sequence `BBA`
removes `7+7+1=15` zeros. The lower B-triad removes 7, so its left-side
conjugacy is exactly

```
rhoZero(ell-7) = rhoZero(ell) - 15.
```

Every finite `ell` seen in the reachable family satisfies this identity.
The right side after `BBA` is

```
1^6 0 1^13 0^(2*a-3) 1^(rho(b)+3) ...
```

and this is exactly the right-run renormalization of the lower B result

```
1^2 0 1^5 0^(a-1) 1^(b+3) ...
```

including the terminal/nonterminal case for the `b` block.

Finally, when the lower A-triad is the carry case `b=5`, the raised
configuration has second block 13. Its first high A is normal, the following
B exhausts the generated seven-zero runway, and the last high A is the
`b=5` carry. If the lower left begins `1^d 0^ell L`, the two adjacent
raised 1-runs merge to length `2*d+2*a+4`; the carry therefore emits a
first right block of length

```
2*d + 2*a + 10 = 2*(d+a+4)+2,
```

exactly the first-run rule applied to the lower carry output. The remaining
left equality is the one-cell identity

```
rhoZero(ell-1) = rhoZero(ell)-1,
```

which holds on the finite reachable zero-run classes (with the all-blank tail
handled as the obvious infinite-zero case).

The zero-run arithmetic is itself finite-state. Introduce the four classes

```
Z[-1](q) = 8*q-1   (q >= 1)
Z[ 0](q) = 8*q
Z[ 1](q) = 8*q+1
Z[ 2](q) = 8*q+2
```

together with the anchor `3`. Then `rhoZero` simply doubles the class
parameter:

```
rhoZero(Z[s](q)) = Z[s](2*q).
```

The B-triad's subtraction by seven cycles exactly through the classes needed
by its reachable left runway:

```
Z[-1](q)-7 = Z[0](q-1)
Z[ 0](q)-7 = Z[1](q-1)
Z[ 1](q)-7 = Z[2](q-1)
Z[ 2](1)-7 = 3.
```

Consequently `rhoZero(ell-7)=rhoZero(ell)-15` is immediate in every B case.

The A carry's subtraction by one similarly cycles

```
Z[0](q)-1 = Z[-1](q)
Z[1](q)-1 = Z[0](q)
Z[2](q)-1 = Z[1](q),
```

with anchors `3->2` and `1->0` (where 0 means the run disappears into the
blank tail). Hence `rhoZero(ell-1)=rhoZero(ell)-1` is immediate in every
carry case. The normal-A runway is always in `Z[-1]`
(`b-6 = 7,23,55,119,...`), giving
`rhoZero(b-6)=2*b-11`.

Thus the entire **left side** of both conjugacy identities is closed by a
five-state arithmetic grammar: four signed residues plus the anchor 3. The
remaining symbolic-domain work is to package the right alternating-run
shape, terminal/nonterminal final-block flag, and these left classes into a
single invariant and check that the exact A/B triad rewrites preserve it.

## Remaining proof obligation

The infinite proof has therefore narrowed to a local renormalization theorem:
define the symbolic domain of reachable triad-boundary zippers, prove it is
closed under the A/B triad rewrites and under `rho`, and prove the two
conjugacy identities above on that domain. The base epoch `C_2 -> C_3` is
finite. Conjugacy would then inductively lift the whole epoch, proving
`C_n -> C_(n+1)` for every n and simultaneously proving that F1 is never
queried.

The finite checkers deliberately stop short of that domain/conjugacy proof.
Their checkpoint, substitution and renormalization assertions are
computational evidence; the exact local triad rewrites earlier in this note
are the transition-level lemmas intended to discharge the remaining proof.
