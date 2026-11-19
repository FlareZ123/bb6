# P4 root-index stratum r = 32 (mod 64): source-image exclusion

**Status:** paper-level derivation from the existing P4 parent-fan lemma and source-certified inverse/image lemmas. The new even/odd three-divisible parent lemma below has not yet been Lean-formalized or CI-compiled. This closes one root-index stratum only; it is not a Machine C or BB(6) decision.

## Setup

On the remaining B2 branch, the existing exact reduction is
```
B2(u) = (734+10944*u, 34881+518816*u)
CReach(B2(u))  <->  CReach(P4(u))
P4(u) = (63895+950614*u, 3291+48981*u)
```
for `u ≡ 2 (mod 4)`. On the `r ≡ 0 (mod 8)` subbranch, write
```
u = 122 + 840*w
x = P4.x = 116038803 + 798515760*w
y = P4.y = 5978973 + 41144040*w
S = x+y = 122017776 + 839659800*w
X = x+2*y = 127996749 + 880803840*w.
```
The established exact valuation identity is
```
v2(S) = v2(2570932352 + 3163718175*r).
```
If `r ≡ 32 (mod 64)`, then `v2(S)=5`. Equivalently, from the displayed affine expression in `w`, `w ≡ 2 (mod 8)`. Put `w=2+8t`; then `u=1802+6720*t`.

The three-divisible odd/odd parent fan already derived for P4 says every source predecessor has an even depth `n` with `n+2 ≤ v2(S)`. Thus at valuation five the only possible depths are `n=0,2`.

## Depth zero parent is unreachable

The `n=0` parent is
```
P0 = (61008886+419829900*w,
      33493928+230486970*w).
```
For `w=2+8*t`,
```
P0 = (900668686+3358639200*t,
      494467868+1843895760*t).
```
It is even/even, its right coordinate is at least six, and
```
P0.x + P0.y = 1395136554 + 5202534960*t ≡ 2 (mod 4).
```
The source-certified even/even parent fan therefore leaves only the direct parent:
```
D0 = (1395136552+5202534960*t,
      247233933+921947880*t).
```
Here `D0.x>5`, `D0.y≥5`, `D0.y` is odd, and
```
D0.x + D0.y = 1642370485 + 6124482840*t ≡ 1 (mod 4).
```
The source-certified `blank_no_odd_sum_one` excludes D0. Hence P0 is not blank-reachable.

## Correct depth two parent and its exclusion

The exact `n=2` equations are
```
a2 = S/8 - 2 = 15252220 + 104957475*w
k2 = (X-a2-13)/2 = (112744516 + 775846365*w)/2.
```
The half-unit term is essential. Since `w` is even, write `w=2*z`; then
```
P2 = (15252220+209914950*z,
      56372258+775846365*z).
```
For `w ≡ 2 (mod 8)`, `z ≡ 1 (mod 4)`; write `z=4*t+1`. Thus
```
P2 = (225167170+839659800*t,
      832218623+3103385460*t).
```
This is an even/odd state, not even/even. Its right coordinate is odd and at least five. Its coordinate sum is
```
T = P2.x+P2.y = 1057385793 + 3943045260*t,
T+1 = 2*(528692897 + 1971522630*t).
```
The factor in parentheses is odd, so `v2(T+1)=1`. Also `3 | T`: both displayed coefficients are divisible by three.

### New source-parent lemma: even/odd target with 3-divisible sum

Suppose `x` is even, `y` is odd with `y≥5`, and `3 | x+y`. If
```
secNext (a,k) = some (x,y),
```
then the complete original-source grammar forces `a` odd and an even `n` such that
```
x+y+1 = 2^n*(2*a+6)
2*k+a+7+3*n = x+2*y.
```
In particular, `4 | x+y+1`.

Proof by exhaustive cases of `section_preimage_all_iff`:

1. The `a=0` nonexceptional branch requires `x+y=8*2^n`, impossible since `3 | x+y`; its exceptional outputs have right coordinate at most four.
2. The `a=1` exceptional outputs have coordinate sum seven, not divisible by three. Its high branch has `x+y+1=16*2^n`; cost parity forces `n` odd, while modulo three the right side is then two and the left side is one.
3. The `k=0` and direct branches have even right coordinate, contrary to odd `y`.
4. The even-`a` bounce branch has even `x+y), contrary to the target parity.
5. Only the odd-`a` bounce remains. Its source equations simplify to the two displayed equations. Cost parity forces `n` even. Since `a` is odd, `2*a+6=2*(a+3)` is divisible by four, proving `4 | x+y+1`.

Applying this lemma to P2 would require `4 | T+1`, contradicting `v2(T+1)=1`. Therefore P2 has no source predecessor at all and is not blank-reachable.

## Consequence

At `r ≡ 32 (mod 64)`, P4 has only the `n=0` and `n=2` source-parent possibilities. Both P0 and P2 are unreachable, so P4 is unreachable. The existing B2-to-P4 equivalence then gives the infinite exclusion
```
u ≡ 1802 (mod 6720)
  => not CReach(734+10944*u, 34881+518816*u).
```
By the exact root-index valuation identity, this is the `r ≡ 32 (mod 64)` stratum of the remaining B2 branch.

## Remaining work

- Formalize the even/odd three-divisible parent lemma from the original `section_preimage_all_iff`.
- Compose the n=0/n=2 exclusions with the existing B2-to-P4 equivalence in Lean and run the existing manual source-verification workflow.
- Continue with `r ≡ 0 (mod 64)` (where n≥4 may occur), `r ≡ 16 (mod 32)`, and `r ≡ 8 (mod 16)`. No claim is made about those strata.
