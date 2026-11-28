# Raw11 q0-148: exact even-gap carry normal forms and the three-turn source bridge

**Status, 2026-11-28:** Concrete all-length symbolic proof candidates and a 150-case direct original-table regression. Source Lean files are committed; **kernel acceptance is pending**. These are intermediate results, **not** a source Cover, a proof of full q0-148 nonhalting, or a BB(6) solution.

## Original source and the missing bridge

One-hole table `1RB1LC_1RC0RE_0LA0LD_1LA0RF_1RB1RD_0RC---`; the missing entry is F1. Agent5's exact open-table macros are in `../agent5-weighted-tnf-queue/Q0148BoundarySweep.lean`: `carryFold`, `twoBlankTurns`, `anotherBlankCycle`, `ARightToEOne`, and `markedHopN`. The proposed boundary arithmetic invariant/return is in `../agent5-weighted-tnf-queue/q0-148-boundary-recurrence.md`. The challenge is to prove that *the actual raw source machine* has the proposed positive return, not merely to prove that the gap-vector map preserves an abstract language.

Define chunk alphabet `A=alternating` (bits `10`), `M=separatedMarker` (bits `11010`), and carries `S=eleven`, `T=elevenZeroOne`, `U=one`. For a finite natural-number list `ns=[n₁,...,n_k]` let
```
 E(ns) = A^(2n₁) M ... A^(2n_k) M
 N(ns) = M A^(2n₁) ... M A^(2n_k).
```
These definitions work for arbitrary k and all n_i≥0; no simulation cutoff or cardinality assumption is involved. The precise all-length transducer laws are
```
 carryFold U (A^r M) = (A^(r+2),S)
 carryFold S (A^(2r) M) = (M A^(2r),S)
 carryFold S E(ns) = (N(ns),S).
```
In particular, `N(ns) M = M E(ns)` as literal chunk lists. This identity means `carryFold` **preserves all even gap lengths while moving the markers** rather than just returning the same carry.

## The harder a=3 branch resolves in exactly two additional cycles

For the qE right-blank boundary chunk stream `C=E(ns) A A`, write `s=scanCost(C)`. Successive exact carry outputs are:
```
 stage 0, twoBlankTurns:
   carryFold S C                = (N(ns) M, U)
   next input chunks            = M N(ns) M

 stage 1, anotherBlankCycle with tok=A:
   carryFold S (M N(ns) M A)    = (M M N(ns), T)

 stage 2, anotherBlankCycle with tok=M:
   carryFold S (M M N(ns) M)    = (M M M N(ns), S).
```
Each equality follows by finite-state word induction, marker rotation and the existing exact source transducer. Symbolic source times simplify to
```
  twoBlankTurns:           5s + 26
  U-to-T blank cycle:     4s + 38
  T-to-S blank cycle:     4s + 50
  total:                 13s +114.
```
The original physical word length is `B=s+4`, so the combined source time is `13B+62`. The **output state is qA0 with leading right tape `1010 ++ outputBits(M M M N(ns))`**, and qA's left tape is blank up to the arbitrary untouched suffix. Three leading `M` markers versus one in the a=1 branch account algebraically for the **two additional markers** in Agent5's proposed a=3 gap recurrence, with the interior gaps untouched at this stage.

The second Lean root `Q0148ThreeCarryCycles.lean` expresses this as `three_blank_turns_source` by composing `twoBlankTurns` and `anotherBlankCycle` twice with **seven blank left padding bits and three extra blank right padding bits**. These explicit paddings prevent silently assuming an extra blank when joining finite-source computations. The theorem's conclusion is a strict **defined original-table run** for every finite `ns` and arbitrary untouched external tails `L,R`. Lean acceptance remains to be established.

The simpler a=1 case has `C=E(ns)`, normalized carry `S`, qA0 after `5s+26` original steps, and leading right tape `1010 ++ outputBits(M N(ns))`. For either case, when `ns=prefix++[n]`, the right tape begins `(10)^(2n+2) 110`, so the existing `ARightToEOne (2n)` source lemma can enter the leftmost E1 marker in another `4n+6` steps. Formalizing the full right-return and the following `markedHopN` sequence remains the decisive unsolved piece.

## Reproduction and proof status

- `Q0148EvenCarryOutput.lean`: even-gap output and list factorization, five named `*_output` theorems for the generic `shared-lean-source-closure.yml` source audit.
- `Q0148ThreeCarryCycles.lean`: marker rotation, second/third carry formulas and exact-source three-cycle composition. These files import the existing source macro module rather than rebuilding or replacing source semantics.
- Direct independent JS interpretation of the literal original partial table checked **150 parametrically chosen finite `ns` lists** of up to seven blocks, with different arbitrary left/right nonblank tails, at exactly `13s+114` source steps. All 150 yielded the predicted qA0 head and complete named output tape prefix/tail; this is an internal finite regression, **not** proof of universal validity. The Lean files contain the mathematical generalization and are the authoritative proof target.

**Next action:** source-compile the two new files against pinned Lean 4.36.0-rc2, repair any failing goals, then use the exact right-output factorization to join the original `ARightToEOne` and `markedHopN` macros into the universal positive boundary return. Do not mistake a successful source subroutine for the full raw one-hole Cover.
