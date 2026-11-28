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

## Remaining proof obligation

A proof of the infinite family should define a symbolic configuration grammar
closed by the two exact triad rewrites and prove that its induced triad word is
the substitution fixed family above. That would simultaneously prove that F1
is never queried and derive `C_n -> C_(n+1)` for all n.

The finite checker `analyze_17557_dyadic.py` deliberately stops short of that
induction: its checkpoint and substitution assertions are computational
evidence for the missing global grammar, while the two local triad rewrites in
this note identify the exact symbolic lemmas to formalize.
