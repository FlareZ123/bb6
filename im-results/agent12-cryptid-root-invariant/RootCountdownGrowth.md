# Withdrawn root countdown and growth family (pre-head-one simulator)

**Status: WITHDRAWN as source dynamics.** The simulator omitted the source DR right-head-one token branch. The corrected b<=1 replay falsifies the tested D_n(c) countdown endpoints and the DR/G/B 76-step endpoint. The root connection and all downstream macro indices below are historical outputs of the defective successor. See [DRHeadOneCycle.md](../agent48-cryptid-root-cycle/DRHeadOneCycle.md).

## Historical experiment (not source-valid)

## 1. The root reaches a one-counter corridor

The corrected root prefix reaches

`EL(L=[0],R=[0,546])`

at macro index 22,083. Sixteen further successors give

`D_0(540)=CR(L=[0],R=0^5 ++ [540])`

at macro index 22,099.

Define the parameterized states

```text
D_n(c) = CR(L=[0], R=0^(4n+5) ++ [c]).
```

The observed triangular countdown macro is

```text
S^(8n+24)(D_n(c)) = D_(n+1)(c-3),   c >= 3.
```

It has been checked by the array-based source-successor simulator for
`n=0,...,6` and `c=3,4,5,10,540`. This is the candidate general identity;
its proof should compose the ordinary CR/EL/DL/DR clauses and is a priority
formalization target.

For the root's first counter value, iterating the formula 180 times gives:

| State | Macro index |
|---|---:|
| `D_0(540)` | 22,099 |
| `D_179(3)` | 153,843 |
| `D_180(0)` | 155,299 |

The elapsed time from `D_0(540)` to `D_180(0)` is
`sum_(n=0)^179 (8n+24) = 133,200`.

## 2. The zero counter resets upward

The exact 1,481-step source-successor run from

```text
D_180(0) = CR(L=[0], R=0^726)
```

reaches

```text
D_0(1453) = CR(L=[0], R=0^5 ++ [1453]).
```

This is a finite computationally checked reset, not yet a symbolic theorem.
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

The 76-step macro is

```text
S^76(DR(L=G, R=[1] ++ B ++ T))
  = DR(L=G, R=[1] ++ B ++ B ++ T).
```

The left list is unchanged. One copy of the 12-entry block `B` is inserted
immediately after the leading 1, and the old suffix is preserved verbatim.
The 76-step path uses only ordinary CR/EL/DL/DR transitions and invokes no
token normalizer.

The identity was checked with suffixes
`[]`, `[0]`, `[1]`, `[3,0,0]`, `[7,5,3,1]`, and
`[12,0,0,0,12,0,0,0,2]`. An opaque object sentinel at the end also survived
unchanged, providing a direct test that the macro does not inspect the tail.
The actual root-reachable state was also advanced 76 steps and matched the
same block insertion.

Consequently, if the 76-step identity is proved against the source successor,
it yields an infinite projected orbit from the root-reachable state at macro
1,153,484: after (k) macro iterations the right list contains (k) further
copies of (B), so its length is unbounded and the path cannot terminate
inside the projected system.

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

The current evidence is a promising root-to-growth construction, not a
completed nonhalting proof. The essential obligations are:

1. Prove the general countdown identity
   `S^(8n+24)(D_n(c)) = D_(n+1)(c-3)` for all `n>=0,c>=3`.
2. Prove the 1,481-step reset `D_180(0) -> D_0(1453)` against the source
   stack successor.
3. Certify the 50,000-step path from `D_484(1)` to
   `DR(G,[1]++B++T)`, preferably by discovering shorter macro blocks.
4. Prove the 76-step tail-parametric block-insertion identity against the
   actual source definitions.
5. Lift the projected infinite path through the original TM/source
   correspondence, with no omitted halting branch.

The 76-step growth identity is the highest-value immediate Lean target: it is
short, uses no token normalizers, and proves unbounded right-stack growth from
any state in the displayed family. The finite root prefix can then be
compressed separately.

## 5. Reproducibility and source status

The corrected token normalizer is documented in
[TokenNormalizerCorrection.md](TokenNormalizerCorrection.md). The updated
`verify_root_corridor_macro.js` now contains tests for the countdown samples,
the 1,481-step reset, the 50,000-step root-to-growth prefix, and the
tail-parametric 76-step macro. It has not yet been executed under Node/CI
after editing. The corresponding manual V8 checks passed. No Lean theorem or
original-TM nonhalting claim is made.
