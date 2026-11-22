# Withdrawn root countdown and growth family (pre-head-one simulator)

**Status: WITHDRAWN as source dynamics.** The simulator omitted the source DR right-head-one token branch. The corrected b<=1 replay falsifies the tested D_n(c) countdown endpoints and the DR/G/B 76-step endpoint. The root connection and all downstream macro indices below are historical outputs of the defective successor. See [DRHeadOneCycle.md](../agent48-cryptid-root-cycle/DRHeadOneCycle.md).

## Historical experiment (not source-valid)

## 1. The root reaches a one-counter corridor

The pre-head-one simulator reported EL(L=[0],R=[0,546]) at macro 22,083 and D_0(540) at macro 22,099. Both states and indices are withdrawn as source claims; the corrected root instead follows the recurrence in [DRHeadOneCycle.md](../agent48-cryptid-root-cycle/DRHeadOneCycle.md).

Define the parameterized states

```text
D_n(c) = CR(L=[0], R=0^(4n+5) ++ [c]).
```

The old simulator claimed the triangular countdown macro

```text
S^(8n+24)(D_n(c)) = D_(n+1)(c-3),   c >= 3.
```

The earlier sample checks used the defective successor. A replay with the r1=1 token branch falsifies the claimed endpoints for every tested n=0,...,6 and c=3,4,5,10,540. This is not a formalization target.

For the root's first counter value, iterating the formula 180 times gives:

| State | Macro index |
|---|---:|
| `D_0(540)` | 22,099 |
| `D_179(3)` | 153,843 |
| `D_180(0)` | 155,299 |

The elapsed time from `D_0(540)` to `D_180(0)` is
`sum_(n=0)^179 (8n+24) = 133,200`.

## 2. The zero counter resets upward

The old simulator reported a 1,481-step run from

```text
D_180(0) = CR(L=[0], R=0^726)
```

reaches

```text
D_0(1453) = CR(L=[0], R=0^5 ++ [1453]).
```

This reset is a historical output of the defective successor, not a source-valid run.
The second countdown starts with counter 1453. Since
`1453 - 3*484 = 1`, 484 applications of the triangular macro reach

```text
D_484(1) = CR(L=[0], R=0^1941 ++ [1])
```

after

`sum_(n=0)^483 (8n+24) = 946,704`

additional successors, at macro index 1,103,484.

## 3. A root-reachable tail-parametric growth macro

A further 50,000 source-successor steps from `D_484(1)` reach macro index
1,153,484 in the state

```text
DR(L=G, R=[1] ++ B ++ T)
```

where

```text
G = [0,0,1,0,1,0,0,0,0,1]
B = [16,0,0,0,2,0,0,0,2,0,0,0]
```

and `T` is the remaining finite right-list suffix. The actual state had
right-list length 7,330; its first 13 entries were exactly `[1] ++ B`.

The old simulator claimed the 76-step macro

```text
S^76(DR(L=G, R=[1] ++ B ++ T))
  = DR(L=G, R=[1] ++ B ++ B ++ T).
```

The corrected replay invokes the source-required DR token closure and does not reach this endpoint. The claimed insertion identity is withdrawn as a source-stack result.

The identity was checked with suffixes
`[]`, `[0]`, `[1]`, `[3,0,0]`, `[7,5,3,1]`, and
`[12,0,0,0,12,0,0,0,2]`. An opaque object sentinel at the end also survived
unchanged, providing a direct test that the macro does not inspect the tail.
The actual root-reachable state was also advanced 76 steps and matched the
same block insertion.

The claimed root-reachable infinite-orbit conclusion is withdrawn. The old root prefix and the 76-step endpoint both fail under the corrected source branch.

For a compact control-state certificate, the 76 transitions have this
run-length encoding of mode labels:

```text
DR^3 CR^7 EL DL EL^4 DL EL^2 DL EL^2 DL EL^2 DL
DR^3 CR^4 EL^3 DL EL^2 DL DR^3 CR^13 EL^2 DL
DR^3 EL DL EL^5 DL EL^2 DL EL^2 DL
```

The full test is tail-parametric, includes the opaque sentinel, and asserts
zero token-normalizer calls.

## 4. What remains to prove

The previous evidence was a root-to-growth construction in the defective simulator and is withdrawn. The current formalization target is:

1. Prove DR([0,0],[1]) -> CR([0,0,1],[1]) in 19 raw steps.
2. Prove CR([0,0,1],[c]) -> CR([0,0,1],[c+5]) in 36 raw steps for c>=1.
3. Compose with the seven-step #490 blank-root entry and audit the lifted execution.

The parameterized 36-step recurrence in DRHeadOneCycle.md is now the highest-value Lean target; it includes the required token closure.

## 5. Reproducibility and source status

The corrected token normalizer is documented in
[TokenNormalizerCorrection.md](TokenNormalizerCorrection.md). The updated verify_root_corridor_macro.js now tests the corrected root cycle and asserts that the old countdown/H-phase/DR-G-B endpoints do not survive. It has not been executed under Node/CI. The equivalent V8 replay supports the new cycle. No Lean theorem or original-TM nonhalting claim is made.
