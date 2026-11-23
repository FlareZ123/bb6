# M32 high quotient: non-overlap with the six-forced filter

Status: the M32 source exclusion is already kernel-backed in Agent 4's `HighSource.lean`; the exact CThreeSix integration is in `CThreeSixM32Integration.lean` and its combined CI run is pending. The finite mask intersection below was computed by evaluating the checked M32 `highPairGood` predicate and the exact `sixForcedExcluded` normalizer. The residue argument proving that the listed family survives six-forced is elementary and should be formalized in Lean.

## Eight residue pairs

The M32 high quotient forbids 492 of the 1,024 `(j,m) mod 32` pairs. Comparing that mask with `sixForcedExcluded` gives eight forbidden pairs on which the six-forced normalizer does not exclude the high target:

```
(j mod 32, m mod 32):
( 0,13) ( 4,25) ( 8, 5) (12,17)
(16,29) (20, 9) (24,21) (28, 1)
```

Equivalently, these are exactly
```
j % 4 = 0
m % 32 = (3*j + 13) % 32
```
There are eight such pairs because `j % 32` can be any of `0,4,8,12,16,20,24,28`.

All eight are admitted by the M16 high mask. Thus these are genuinely new M32 exclusions relative to both M16 and the six-forced filter.

## Why six-forced does not fire

Let the high stopping target be
```
x = 2*j + 3
k = 2^(2*m+2)*(j+3) - (j+3*m+5)
```
with `m >= 2`, `j % 4 = 0`, and `m % 32 = (3*j+13) % 32`.

Since `m >= 2`, the power term is divisible by 8. The residue hypotheses give
```
x % 8 = 3
(j + 3*m + 5) % 8 = 4
k % 8 = 4
(x + k) % 8 = 7
(x + k) % 4 = 3
x % 16 in {3,11}
```
Consequently:
- `oddLowGate` cannot fire because `k` is even.
- `evenSevenGate` and `evenOddFourGate` cannot fire because `x` is odd.
- `evenAffineGate` cannot fire because `(x+k) % 4 = 3), not 1.
- `sixEvenRightGate` cannot fire because `(x+k) % 8 = 7).
- `valSixGate` cannot fire because `x % 16` is 3 or 11, not 5.
- The terminal exclusion also fails because `k` is even.

Thus `sixForcedNormalize x k = (x,k)` and `sixForcedExcluded x k = false` throughout these eight residue families, independently of higher lifts.

## What M32 adds

The checked M32 predicate `CCert.highPairGood (j % 32) (m % 32)` is true on all eight pairs. Agent 4's source theorem `BB6.Agent4M32.high32_forbidden_source` therefore proves the original CLine target unreachable for every lift with `j >= 3`, `m >= 2`, and the exact high stopping equation.

The integration module `CThreeSixM32Integration.lean` adds the full 492-pair M32 condition to the existing CThreeSix exact criterion, not merely these eight examples. The non-overlap family is a useful strictness witness: M32 contributes source exclusions that the current six-forced normalizer cannot see.
